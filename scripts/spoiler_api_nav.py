#!/usr/bin/env python3
"""Post-process the doc-gen4 API reference navbar.

doc-gen4 emits a single shared ``navbar.html`` (loaded into every page via an
``<iframe class="navframe">``). Its ``<div class="module_list">`` lists every
top-level module as a ``<details class="nav_sect">`` block — for this project
that means our own ``Langlib`` module buried among ~12 dependency trees
(Mathlib, Lean core, Batteries, Aesop, …), which dwarf it.

This script "hijacks" that navbar so the project module stays front and centre:
it hoists the kept module (``Langlib`` by default) to the top of the list, folds
every *other* top-level module into a single collapsible ``<details>`` "spoiler"
(collapsed by default), and also folds the "General documentation" section into
its own collapsible spoiler — leaving only the project module on display.

Only ``navbar.html`` is rewritten — because it is shared, the change shows up on
every page. The operation is idempotent (re-running is a no-op) so it is safe to
wire into the docs deploy.

Usage:
    scripts/spoiler_api_nav.py DOC_DIR [options]

    DOC_DIR          Directory containing the doc-gen4 output (the one with
                     navbar.html, e.g. .lake/build/doc or an extracted _site/api).

Options:
    --keep NAME      Module to keep visible at the top (default: Langlib).
    --label TEXT     Summary text of the dependencies spoiler (default:
                     "Dependencies").
    --open           Render the spoilers expanded by default (default: collapsed).
    --keep-general   Leave the "General documentation" section unfolded.
    --check          Exit non-zero without writing if the navbar is not yet
                     folded (useful in CI to assert the step ran).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# Marker classes on the generated spoilers; also used to detect prior runs.
MARKER_CLASS = "langlib-nav-folded"
GENDOC_MARKER = "langlib-gendoc-folded"
DEFAULT_LABEL = "Dependencies"
GENDOC_HEADING = "<h3>General documentation</h3>"

MODULE_LIST_OPEN = '<div class="module_list">'
_DETAILS_TOKEN = re.compile(r"<details\b[^>]*>|</details>", re.IGNORECASE)
_DATA_PATH = re.compile(r'data-path="([^"]*)"')


def _module_name(data_path: str | None) -> str | None:
    """Module name from a nav data-path, e.g. './Langlib.html' -> 'Langlib'."""
    if not data_path:
        return None
    m = re.search(r"([^/]+)\.html$", data_path)
    return m.group(1) if m else None


def _top_level_details(html: str, start: int) -> list[tuple[int, int, str | None]]:
    """Spans of the top-level <details> blocks beginning at ``start``.

    ``start`` must point just past ``<div class="module_list">``. Returns a list
    of ``(block_start, block_end, data_path)`` for each direct-child <details>,
    stopping at the first non-<details> content (the closing </div>).
    """
    blocks: list[tuple[int, int, str | None]] = []
    i = start
    n = len(html)
    while i < n:
        # Skip whitespace between sibling blocks.
        while i < n and html[i].isspace():
            i += 1
        if not html.lower().startswith("<details", i):
            break  # reached </div> (end of module_list) or other content
        open_match = _DETAILS_TOKEN.match(html, i)
        assert open_match and not open_match.group(0).startswith("</")
        depth = 1
        j = open_match.end()
        while depth > 0:
            tok = _DETAILS_TOKEN.search(html, j)
            if not tok:
                raise ValueError("unbalanced <details> in navbar.html")
            depth += -1 if tok.group(0).startswith("</") else 1
            j = tok.end()
        dp = _DATA_PATH.search(open_match.group(0))
        blocks.append((open_match.start(), j, dp.group(1) if dp else None))
        i = j
    return blocks


def fold_navbar(html: str, keep: str, label: str, open_spoiler: bool) -> str:
    """Return ``html`` with non-kept top-level modules folded into a spoiler."""
    if MARKER_CLASS in html:
        return html  # already folded — idempotent no-op

    list_open = html.find(MODULE_LIST_OPEN)
    if list_open == -1:
        raise ValueError('could not find <div class="module_list"> in navbar.html')
    content_start = list_open + len(MODULE_LIST_OPEN)

    blocks = _top_level_details(html, content_start)
    if not blocks:
        raise ValueError("module_list contained no top-level <details> blocks")

    kept = [b for b in blocks if _module_name(b[2]) == keep]
    if not kept:
        names = ", ".join(sorted({_module_name(b[2]) or "?" for b in blocks}))
        raise ValueError(f"kept module {keep!r} not found among: {names}")
    others = [b for b in blocks if _module_name(b[2]) != keep]
    if not others:
        return html  # nothing to fold (only the kept module is present)

    sub = lambda b: html[b[0] : b[1]]
    kept_html = "".join(sub(b) for b in kept)
    others_html = "".join(sub(b) for b in others)
    open_attr = " open=\"\"" if open_spoiler else ""
    spoiler = (
        f'<details class="nav_sect {MARKER_CLASS}"{open_attr}>'
        f"<summary>{label}</summary>{others_html}</details>"
    )

    region_start, region_end = blocks[0][0], blocks[-1][1]
    return html[:region_start] + kept_html + spoiler + html[region_end:]


def fold_general_docs(html: str, open_spoiler: bool) -> str:
    """Fold the "General documentation" section into its own collapsible spoiler.

    Wraps the section heading and the links that follow it (up to the next
    ``<h3>``) in a ``<details>``, turning the heading into the summary.
    """
    if GENDOC_MARKER in html:
        return html  # already folded — idempotent no-op

    start = html.find(GENDOC_HEADING)
    if start == -1:
        return html  # no such section — nothing to fold
    content_start = start + len(GENDOC_HEADING)
    section_end = html.find("<h3>", content_start)
    if section_end == -1:
        raise ValueError('no <h3> follows "General documentation"; cannot bound the section')

    inner = html[content_start:section_end]
    open_attr = " open=\"\"" if open_spoiler else ""
    spoiler = (
        f'<details class="nav_sect {GENDOC_MARKER}"{open_attr}>'
        f"<summary>General documentation</summary>{inner}</details>"
    )
    return html[:start] + spoiler + html[section_end:]


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("doc_dir", type=Path, help="doc-gen4 output dir (contains navbar.html)")
    parser.add_argument("--keep", default="Langlib", help="module kept visible at the top")
    parser.add_argument("--label", default=DEFAULT_LABEL, help="spoiler summary text")
    parser.add_argument("--open", action="store_true", dest="open_spoiler", help="render the spoilers expanded")
    parser.add_argument("--keep-general", action="store_true", help='leave the "General documentation" section unfolded')
    parser.add_argument("--check", action="store_true", help="fail (without writing) if not already folded")
    args = parser.parse_args(argv)

    navbar = args.doc_dir / "navbar.html"
    if not navbar.is_file():
        print(f"error: {navbar} not found", file=sys.stderr)
        return 2

    html = navbar.read_text(encoding="utf-8")

    if args.check:
        ok = MARKER_CLASS in html
        print(f"{'folded' if ok else 'NOT folded'}: {navbar}")
        return 0 if ok else 1

    try:
        folded = fold_navbar(html, args.keep, args.label, args.open_spoiler)
        if not args.keep_general:
            folded = fold_general_docs(folded, args.open_spoiler)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    if folded == html:
        print(f"navbar already folded (no change): {navbar}")
        return 0

    navbar.write_text(folded, encoding="utf-8")
    extra = "" if args.keep_general else " + general docs"
    print(f"folded navbar: kept {args.keep!r} at top, spoilered the rest{extra} -> {navbar}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
