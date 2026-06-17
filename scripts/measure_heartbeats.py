#!/usr/bin/env python3
"""Measure elaboration *heartbeats* of the Langlib sources.

Heartbeats are Lean's deterministic measure of elaboration work (the same unit as
`set_option maxHeartbeats`). Unlike wall-clock time they are reproducible, which
makes them ideal for tracking proof cost and catching regressions.

Two modes:

* default (per-file total): appends a probe that reads the cumulative heartbeat
  counter at the end of the file. Each declaration runs under its real budget
  (the file's own `set_option maxHeartbeats`), so the number is exactly what the
  build spends -- and nothing can run away, because every declaration is capped
  just as it is during `lake build`.

* `--per-decl`: drives Mathlib's `countHeartbeats` linter to report every
  declaration separately. This is great for finding hotspots, but it measures
  each declaration with an *unlimited* budget, so a pathological declaration can
  be slow; the wall-clock timeout (and process-group kill) bounds the damage.

Both modes run with `Elab.async=false`. Under Lean's `module` system theorem
bodies elaborate on worker threads, but the heartbeat counter is thread-local, so
with async enabled the measurement only sees a declaration's signature. Disabling
async forces synchronous elaboration so the numbers are real.

Heartbeat figures are user-facing (internal counter / 1000), matching
`set_option maxHeartbeats`.

Usage:
    scripts/measure_heartbeats.py                 # per-file totals for all of src/
    scripts/measure_heartbeats.py FILE [FILE...]  # specific files
    scripts/measure_heartbeats.py --per-decl FILE # per-declaration breakdown
    scripts/measure_heartbeats.py -j 8 -o hb.tsv
"""
from __future__ import annotations

import argparse
import concurrent.futures
import os
import re
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
USED_RE = re.compile(r"^'([^']+)' used (\d+) heartbeats")
TOTAL_RE = re.compile(r"HEARTBEATS_TOTAL (\d+)")
# A `set_option maxHeartbeats N` line, standalone or as a `... in` wrapper.
MAXHB_RE = re.compile(r"^\s*set_option maxHeartbeats \d+( in)?\s*$")
# Default budget for declarations that have no explicit cap (mirrors a generous
# build). Only used in --per-decl mode for the ordinary elaboration pass.
DEFAULT_CAP = 4_000_000
TIMEOUT = int(os.environ.get("HB_TIMEOUT", "600"))

PROBE = (
    "\nopen Lean in\n"
    "run_cmd do Lean.logInfo m!\"HEARTBEATS_TOTAL {(← IO.getNumHeartbeats) / 1000}\"\n"
)


def _run_lean(args: list[str]) -> "subprocess.CompletedProcess | None":
    """Run lean in its own session; kill the whole group on timeout (so the
    `lean` grandchild of `lake` cannot orphan and keep burning CPU)."""
    proc = subprocess.Popen(
        ["lake", "env", "lean", *args],
        cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True,
    )
    try:
        out, err = proc.communicate(timeout=TIMEOUT)
        proc.stdout_data, proc.stderr_data = out, err
        return proc
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait()
        return None


def measure_total(path: Path) -> list[tuple[int, str, str]]:
    """Per-file cumulative heartbeats via an appended probe (safe, bounded)."""
    rel = os.path.relpath(path, REPO)
    text = path.read_text() + PROBE
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
        tf.write(text)
        tmp_path = tf.name
    try:
        proc = _run_lean(["-DElab.async=false", tmp_path])
    finally:
        os.unlink(tmp_path)
    if proc is None:
        return [(-1, "TIMEOUT", rel)]
    blob = proc.stdout_data + proc.stderr_data
    m = TOTAL_RE.search(blob)
    return [(int(m.group(1)), "<file total>", rel)] if m else [(-2, "NO_TOTAL", rel)]


def measure_per_decl(path: Path) -> list[tuple[int, str, str]]:
    """Per-declaration heartbeats via the countHeartbeats linter.

    Strips the file's `set_option maxHeartbeats` lines: a `maxHeartbeats N in`
    wrapper makes the linter report only the declaration's signature cost, so we
    drop the wrappers and give the ordinary pass a generous global cap instead.
    """
    rel = os.path.relpath(path, REPO)
    stripped = "".join(
        "" if MAXHB_RE.match(line) else line + "\n"
        for line in path.read_text().splitlines()
    )
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
        tf.write(stripped)
        tmp_path = tf.name
    try:
        proc = _run_lean([
            f"-DmaxHeartbeats={DEFAULT_CAP}",
            "-DElab.async=false",
            "-Dlinter.countHeartbeats=true",
            tmp_path,
        ])
    finally:
        os.unlink(tmp_path)
    if proc is None:
        return [(-1, "TIMEOUT", rel)]
    out = []
    for line in (proc.stdout_data + proc.stderr_data).splitlines():
        m = USED_RE.match(line.strip())
        if m:
            out.append((int(m.group(2)), m.group(1), rel))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*", help="Lean files (default: all of src/)")
    ap.add_argument("--per-decl", action="store_true",
                    help="report each declaration instead of a per-file total")
    ap.add_argument("--jobs", "-j", type=int, default=min(8, os.cpu_count() or 4))
    ap.add_argument("--out", "-o", default="-", help="output TSV path (default: stdout)")
    ap.add_argument("--top", type=int, default=25)
    args = ap.parse_args()

    files = ([Path(f).resolve() for f in args.files]
             if args.files else sorted((REPO / "src").rglob("*.lean")))
    measure = measure_per_decl if args.per_decl else measure_total

    rows: list[tuple[int, str, str]] = []
    by_file: dict[str, int] = {}
    done = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for result in ex.map(measure, files):
            done += 1
            for hb, name, rel in result:
                rows.append((hb, name, rel))
                if hb >= 0:
                    by_file[rel] = by_file.get(rel, 0) + hb
            print(f"\r  measured {done}/{len(files)} files",
                  end="", file=sys.stderr, flush=True)
    print("", file=sys.stderr)

    rows.sort(reverse=True)
    sink = sys.stdout if args.out == "-" else open(args.out, "w")
    try:
        for hb, name, rel in rows:
            print(f"{hb}\t{name}\t{rel}", file=sink)
    finally:
        if sink is not sys.stdout:
            sink.close()

    total = sum(hb for hb, _, _ in rows if hb >= 0)
    bad = [(name, rel) for hb, name, rel in rows if hb < 0]
    print(f"\nTotal heartbeats: {total}", file=sys.stderr)
    print(f"Files/decls measured: {len([r for r in rows if r[0] >= 0])}", file=sys.stderr)
    if bad:
        print(f"Not measured ({len(bad)}): " +
              ", ".join(f"{n}:{r}" for n, r in bad[:10]), file=sys.stderr)
    print(f"\nTop {args.top}:", file=sys.stderr)
    for hb, name, rel in [r for r in rows if r[0] >= 0][:args.top]:
        label = rel if name == "<file total>" else f"{name}  ({rel})"
        print(f"  {hb:>9}  {label}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
