#!/usr/bin/env python3
"""Rewrite expensive `simp`/`simp_all` calls to the `simp only [...]` the prover
actually used.

A bare `simp` searches and indexes the entire simp set on every call; in the
heavy files here individual `simp` calls take seconds. `simp only [<lemmas>]`
replays just the rewrites that fired, which is far cheaper in both time and
heartbeats, and is exactly what `simp?` reports. This tool turns each `simp`
into `simp?`, asks Lean for the `simp only` it suggests, splices that back in,
re-checks the file, and reverts the whole file if anything fails to compile.

Mechanics: everything is done in the *temp* (simp? ) coordinate space and the
result is written back, so we never have to map positions across the inserted
`?` characters. Lean reports the suggestion text in full (config + `only [...]`
+ `at` clause) but the message span only covers the `simp?` head, so we parse the
extent of each original tactic ourselves (balanced brackets, stopping at a
depth-0 tactic terminator).

Usage:
    scripts/replace_simp.py FILE [FILE ...]
    scripts/replace_simp.py --no-verify FILE   # skip per-file recheck (use lake build)
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
# `simp` / `simp_all` used as a tactic, not `simpa`, `dsimp`, `simp_rw`,
# `simp_all`, `simp only`, `simp_all only`, or a qualified name. We deliberately
# skip configured forms (`simp +decide`, `simp (config := ...)`, ...): their
# `simp only` rewrite often fails to reproduce the closing behaviour (e.g. a
# `+decide` discharge), so they are not worth the churn/risk.
_TAIL = r"(?!\w)(?!\?)(?!\s+only)(?!\s*[-+(])"
SIMP_ALL_RE = re.compile(r"(?<![\w.])simp_all" + _TAIL)
SIMP_RE = re.compile(r"(?<![\w.])simp" + _TAIL)
SUGGEST_RE = re.compile(r"\[apply\]\s*(.*)", re.S)
# depth-0 characters that end a tactic invocation
TERMINATORS = set(";\n,⟩⟨·|")


# `simp` as an *attribute* (`@[simp]`, `attribute [simp] foo`, `@[simp, ...]`),
# not a tactic -- must never be turned into `simp?`.
ATTR_RE = re.compile(r"@\[[^\]]*\]|attribute\s*\[[^\]]*\]")


def to_query(text: str) -> str:
    # Positions inside attribute brackets, which we must leave untouched.
    masked = [False] * len(text)
    for m in ATTR_RE.finditer(text):
        for i in range(m.start(), m.end()):
            masked[i] = True

    def repl(tok):
        def f(m):
            return m.group(0) if masked[m.start()] else tok
        return f

    text = SIMP_ALL_RE.sub(repl("simp_all?"), text)
    # Re-mask against the (now possibly shifted) text is unnecessary: simp_all? is
    # never inside an attribute, and we recompute masks only from the original. To
    # stay correct we run the simp pass on the simp_all-substituted text but guard
    # via a fresh attribute scan.
    masked = [False] * len(text)
    for m in ATTR_RE.finditer(text):
        for i in range(m.start(), m.end()):
            masked[i] = True
    text = SIMP_RE.sub(repl("simp?"), text)
    return text


def tactic_extent(text: str, start: int) -> int:
    """Return the index just past the simp invocation whose head starts at
    `start` (head already includes the trailing `?`)."""
    i = start
    depth = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth == 0:
                break
            depth -= 1
        elif depth == 0:
            if c in TERMINATORS:
                break
            if text.startswith("<;>", i):
                break
            if text.startswith("=>", i):
                break
        i += 1
    return i


def lean_json(path: str):
    proc = subprocess.run(
        ["lake", "env", "lean", "-DElab.async=false", "--json", path],
        cwd=REPO, capture_output=True, text=True,
    )
    msgs = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if line:
            try:
                msgs.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    had_error = any(m.get("severity") == "error" for m in msgs)
    return msgs, had_error


def fix_file(rel: str, verify: bool = True) -> str:
    path = REPO / rel
    original = path.read_text()
    if not (SIMP_RE.search(original) or SIMP_ALL_RE.search(original)):
        return "skip (no plain simp)"

    query = to_query(original)
    # Langlib imports are absolute (LEAN_PATH-resolved), so the probe can live
    # in /tmp -- keep generated files out of src/.
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
        tf.write(query)
        qpath = tf.name
    try:
        msgs, had_error = lean_json(qpath)
    finally:
        os.unlink(qpath)
    if had_error and verify:
        return "skip (pre-existing errors)"

    # Collect (offset, suggestion) for each Try-this in query coordinates.
    lines = query.split("\n")
    line_off = [0]
    for ln in lines:
        line_off.append(line_off[-1] + len(ln) + 1)  # +1 for the '\n'

    subs = []
    for m in msgs:
        if "Try this" not in m.get("data", ""):
            continue
        pos = m.get("pos") or {}
        if "line" not in pos:
            continue
        sm = SUGGEST_RE.search(m["data"])
        if not sm:
            continue
        repl = " ".join(sm.group(1).split())
        off = line_off[pos["line"] - 1] + pos["column"]
        if not (query.startswith("simp?", off) or query.startswith("simp_all?", off)):
            continue
        subs.append((off, repl))

    if not subs:
        return "skip (no simp suggestions)"

    def build(keep):
        """Apply the kept subs to `query`; return (text, {output_line: sub_off})."""
        out = query
        for off, repl in sorted(keep, reverse=True):
            end = tactic_extent(out, off)
            out = out[:off] + repl + out[end:]
        # Map each kept sub to its line in the produced text (for error mapping).
        line_of = {}
        delta = 0
        for off, repl in sorted(keep):
            o2 = query  # recompute extent on the ORIGINAL query for stable lengths
            end = tactic_extent(o2, off)
            out_start = off + delta
            line_of[out.count("\n", 0, out_start) + 1] = off
            delta += len(repl) - (end - off)
        return out, line_of

    def restore(text):
        return text.replace("simp_all?", "simp_all").replace("simp?", "simp")

    keep = dict(subs)  # off -> repl
    if not verify:
        out, _ = build(keep.items())
        path.write_text(restore(out))
        return f"APPLIED ({len(keep)} simp -> simp only; verify with lake build)"

    applied = len(keep)
    for _ in range(6):
        out, line_of = build(keep.items())
        path.write_text(restore(out))
        msgs, had_error = lean_json(rel)
        if not had_error:
            return f"OK ({len(keep)}/{applied} simp -> simp only)"
        # Drop the subs on lines that now report errors.
        err_lines = {m["pos"]["line"] for m in msgs
                     if m.get("severity") == "error" and m.get("pos")}
        bad = set()
        for L in err_lines:
            for dl in (0, -1, 1, -2, 2):
                if (L + dl) in line_of:
                    bad.add(line_of[L + dl])
        bad &= set(keep)
        if not bad:
            break
        for off in bad:
            del keep[off]
        if not keep:
            break

    path.write_text(original)
    return f"REVERTED (could not converge; {applied} candidate edits)"


def main() -> int:
    args = [a for a in sys.argv[1:] if a != "--no-verify"]
    verify = "--no-verify" not in sys.argv
    if not args:
        print(__doc__)
        return 1
    for f in args:
        rel = os.path.relpath(Path(f).resolve(), REPO)
        print(f"{rel}: {fix_file(rel, verify=verify)}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
