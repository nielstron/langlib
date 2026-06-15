#!/usr/bin/env python3
"""Replace leftover `exact?` library-search calls with the concrete term they find.

`exact?` runs a whole-environment search on every elaboration, which is one of the
most expensive things a proof can do. Committing `exact?` therefore bakes a large,
non-deterministic heartbeat cost into the build. This tool asks Lean for the term
each `exact?` resolves to (the "Try this:" suggestion, with source positions via
`--json`) and rewrites the call in place, then re-checks the file and reverts if
the rewrite does not compile cleanly.

Usage:
    scripts/replace_exact_q.py FILE [FILE ...]
    scripts/replace_exact_q.py --no-verify FILE   # apply without the per-file
                                                  # re-check; verify with `lake build`

`--no-verify` is useful for files that elaborate fine under `lake build` but
report a spurious error when checked standalone with `lean` (the standalone
invocation lacks lake's `--setup`, which can change e.g. `grind`'s instance set).
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SUGGEST_RE = re.compile(r"\[apply\]\s*(.*)", re.S)


def lean_json(rel: str):
    """Run lean on `rel`, return (messages, had_error)."""
    proc = subprocess.run(
        ["lake", "env", "lean", "-DElab.async=false", "--json", rel],
        cwd=REPO, capture_output=True, text=True,
    )
    msgs = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            msgs.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    had_error = any(m.get("severity") == "error" for m in msgs)
    return msgs, had_error


def collect_suggestions(msgs):
    """Return list of (line, col, replacement) for every `exact?` Try-this message."""
    out = []
    for m in msgs:
        data = m.get("data", "")
        if "Try this" not in data:
            continue
        pos = m.get("pos") or {}
        if "line" not in pos or "column" not in pos:
            continue
        sm = SUGGEST_RE.search(data)
        if not sm:
            continue
        replacement = " ".join(sm.group(1).split())  # collapse whitespace/newlines
        out.append((pos["line"], pos["column"], replacement))
    return out


def fix_file(rel: str, verify: bool = True) -> str:
    path = REPO / rel
    original = path.read_text()
    if "exact?" not in original:
        return "skip (no exact?)"

    msgs, had_error = lean_json(rel)
    if had_error and verify:
        return "skip (file has pre-existing errors)"
    suggestions = collect_suggestions(msgs)
    if not suggestions:
        return "skip (no suggestions found)"

    lines = original.split("\n")
    # Apply from bottom-right to top-left so earlier edits don't shift later positions.
    applied = 0
    for ln, col, repl in sorted(suggestions, reverse=True):
        idx = ln - 1
        if idx >= len(lines):
            continue
        text = lines[idx]
        # Only touch genuine `exact?` calls; other tactics (ring, simp, ...) can
        # also emit "Try this" suggestions which we must leave alone.
        if text[col:col + 6] != "exact?":
            continue
        lines[idx] = text[:col] + repl + text[col + 6:]
        applied += 1

    if applied == 0:
        return "skip (no exact? suggestions applied)"
    new_text = "\n".join(lines)
    path.write_text(new_text)

    if not verify:
        return f"APPLIED ({applied} exact? replaced; verify separately with `lake build`)"

    _, had_error = lean_json(rel)
    if had_error:
        path.write_text(original)
        return f"REVERTED ({applied} edits caused errors)"
    return f"OK ({applied} exact? replaced)"


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
