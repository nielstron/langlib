#!/usr/bin/env python3
"""Per-declaration heartbeat profiler.

Mathlib's `countHeartbeats` linter under-reports under Lean's `module`/async
elaboration, so instead we interleave cumulative-heartbeat probes between
top-level commands and compile once with `Elab.async=false`. The delta between
consecutive probes is the heartbeat cost of the command(s) in between.

A probe is only inserted on a blank line whose next non-blank line begins at
column 0 with a command keyword -- i.e. a genuine top-level command boundary, so
the insertion is always between commands (never inside a proof).

Usage:
    scripts/profile_decls.py FILE          # ranked per-decl heartbeat costs
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
# Tokens that begin a top-level command (possibly as a prefix modifier).
STARTERS = ("theorem", "lemma", "def", "instance", "abbrev", "structure",
            "inductive", "class", "@[", "private", "public", "protected",
            "noncomputable", "set_option", "omit", "namespace", "end", "section",
            "variable", "open", "/--", "/-!", "macro", "elab", "syntax",
            "attribute", "scoped", "mutual", "example", "deriving")
NAME_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |public |protected |noncomputable |scoped )*"
    r"(?:theorem|lemma|def|instance|abbrev|structure|inductive|class|example)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)")
PROBE_RE = re.compile(r"HBPROBE (\d+) (\d+)")


def starts_command(line: str) -> bool:
    return line and line[0] != " " and line[0] != "\t" and \
        any(line.startswith(s) for s in STARTERS)


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 1
    path = (Path(sys.argv[1]).resolve())
    lines = path.read_text().split("\n")

    # Find insertion points: blank line followed (after blanks) by a command start.
    out_lines = []
    probes = []  # (id, name) in order
    pid = 0
    i = 0
    started = False  # only probe after the import header / `section`
    while i < len(lines):
        line = lines[i]
        if not started and (line.strip() in ("public section", "section")
                            or line.startswith("namespace ")):
            started = True
        if started and line.strip() == "":
            j = i + 1
            while j < len(lines) and lines[j].strip() == "":
                j += 1
            if j < len(lines) and starts_command(lines[j]):
                # name of the upcoming declaration (scan a few lines for it)
                name = f"@L{j+1}"
                for k in range(j, min(j + 8, len(lines))):
                    m = NAME_RE.match(lines[k])
                    if m:
                        name = m.group(1)
                        break
                out_lines.append(
                    f'open Lean in run_cmd do Lean.logInfo m!"HBPROBE {pid} '
                    f'{{(← IO.getNumHeartbeats)/1000}}"')
                probes.append((pid, name))
                pid += 1
        out_lines.append(line)
        i += 1
    # final probe
    out_lines.append(
        f'open Lean in run_cmd do Lean.logInfo m!"HBPROBE {pid} '
        f'{{(← IO.getNumHeartbeats)/1000}}"')
    probes.append((pid, "<END>"))

    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
        tf.write("\n".join(out_lines))
        tmp = tf.name
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", "-DElab.async=false", tmp],
            cwd=REPO, capture_output=True, text=True)
    finally:
        os.unlink(tmp)

    vals = {}
    for m in PROBE_RE.finditer(proc.stdout + proc.stderr):
        vals[int(m.group(1))] = int(m.group(2))
    if len(vals) < 2:
        sys.stderr.write("probe parse failed; stderr:\n" + proc.stderr[:2000])
        return 2

    rows = []
    for idx in range(1, len(probes)):
        if idx in vals and (idx - 1) in vals:
            rows.append((vals[idx] - vals[idx - 1], probes[idx - 1][1]))
    rows.sort(reverse=True)
    total = vals.get(max(vals), 0)
    print(f"# {os.path.relpath(path, REPO)}  total={total}  probes={len(vals)}")
    for cost, name in rows:
        print(f"{cost:>8}  {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
