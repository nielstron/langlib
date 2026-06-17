#!/usr/bin/env python3
"""Post-process the doc-gen4 API reference for this project.

doc-gen4 emits a single shared ``navbar.html`` (loaded into every page via an
``<iframe class="navframe">``). Its ``<div class="module_list">`` lists every
top-level module as a ``<details class="nav_sect">`` block — for this project
that means our own ``Langlib`` module buried among ~12 dependency trees
(Mathlib, Lean core, Batteries, Aesop, …), which dwarf it.

This script "hijacks" the reference so the project stays front and centre:

  * In the shared ``navbar.html`` it hoists the kept module (``Langlib`` by
    default) to the top of the list and folds everything else — the other
    top-level modules *and* the "General documentation" section — into one
    collapsible ``<details>`` "spoiler" (collapsed by default).
  * In every page it replaces the generic "Documentation" header title with the
    project logo and name, linking back to the main documentation site (the
    doc-gen4 reference otherwise offers no way back).

The operation is idempotent (re-running is a no-op) so it is safe to wire into
the docs deploy.

Usage:
    scripts/spoiler_api_nav.py DOC_DIR [options]

    DOC_DIR          Directory containing the doc-gen4 output (the one with
                     navbar.html, e.g. .lake/build/doc or an extracted _site/api).

Options:
    --keep NAME      Module to keep visible at the top (default: Langlib).
    --label TEXT     Summary text of the dependencies spoiler (default:
                     "Dependencies").
    --open           Render the spoiler expanded by default (default: collapsed).
    --keep-general   Leave the "General documentation" section in place (do not
                     move it into the dependencies spoiler).
    --home-url URL   Target of the header logo/name link, and base of the logo
                     image (default: derived from the git origin remote, i.e. the
                     repo's GitHub Pages root).
    --home-label TEXT  Text shown beside the logo (default: "Langlib").
    --no-header      Do not rewrite the page header title.
    --check          Exit non-zero without writing if the navbar is not yet
                     folded (useful in CI to assert the step ran).
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

# Marker classes on generated elements; also used to detect prior runs.
MARKER_CLASS = "langlib-nav-folded"
HEADER_MARKER = "langlib-doc-home"
DEFAULT_LABEL = "Dependencies"
DEFAULT_HOME_LABEL = "Langlib"
GENDOC_HEADING = "<h3>General documentation</h3>"

# The generic page-header title doc-gen4 stamps on every page (verbatim & uniform).
HEADER_OLD = '<h1><label for="nav_toggle"></label><span>Documentation</span></h1>'

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


def _general_docs_span(html: str) -> tuple[int, int] | None:
    """(start, end) of the "General documentation" section (its <h3> through the links
    up to the next <h3>), or None if absent. The section sits before the module list."""
    start = html.find(GENDOC_HEADING)
    if start == -1:
        return None
    end = html.find("<h3>", start + len(GENDOC_HEADING))
    if end == -1:
        raise ValueError('no <h3> follows "General documentation"; cannot bound the section')
    return (start, end)


def fold_navbar(html: str, keep: str, label: str, open_spoiler: bool, fold_general: bool) -> str:
    """Hoist the kept module to the top of the module list and fold everything else into a
    single collapsible spoiler. When ``fold_general`` is set, the "General documentation"
    section is moved out of its original spot and into the spoiler too."""
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

    open_attr = " open=\"\"" if open_spoiler else ""

    # The "General documentation" block lives before the module list, so its offsets stay
    # valid after we rewrite the (later) module-list region; we splice it into the spoiler
    # as its own nested collapsible <details> (alongside the dependency modules) and excise
    # the original afterwards.
    gendoc = _general_docs_span(html) if fold_general else None
    gendoc_html = ""
    if gendoc:
        links = html[gendoc[0] + len(GENDOC_HEADING) : gendoc[1]]
        gendoc_html = (
            f'<details class="nav_sect"{open_attr}>'
            f"<summary>General documentation</summary>{links}</details>"
        )

    sub = lambda b: html[b[0] : b[1]]
    # Render the kept module expanded on first visit (doc-gen4 ships it collapsed; nav.js
    # then persists whatever the visitor toggles via sessionStorage).
    kept_html = "".join(re.sub(r"^<details\b", '<details open=""', sub(b), count=1) for b in kept)
    others_html = "".join(sub(b) for b in others)
    spoiler = (
        f'<details class="nav_sect {MARKER_CLASS}"{open_attr}>'
        f"<summary>{label}</summary>{gendoc_html}{others_html}</details>"
    )

    region_start, region_end = blocks[0][0], blocks[-1][1]
    new = html[:region_start] + kept_html + spoiler + html[region_end:]
    if gendoc:  # offsets < region_start, so still valid in `new`; remove the original block
        new = new[: gendoc[0]] + new[gendoc[1] :]
    return new


def rewrite_headers(doc_dir: Path, home_url: str, label: str) -> int:
    """Replace the generic "Documentation" header title on every page with the project
    logo + name, linking back to the main docs site. Returns the number of pages changed.

    Uses absolute URLs (the logo at ``<home>/logo.svg``): doc-gen4 pages reference assets
    by depth-relative paths with no site root, so a single relative path cannot work for
    pages at every depth. Idempotent: once replaced, the old title is gone."""
    new_h1 = (
        '<h1><label for="nav_toggle"></label>'
        f'<a class="{HEADER_MARKER}" href="{home_url}" '
        'style="display:inline-flex;align-items:center;gap:.4em;color:inherit;text-decoration:none">'
        f'<img src="{home_url}logo.svg" alt="" style="height:1.15em;width:auto"/>{label}</a></h1>'
    )
    changed = 0
    for page in sorted(doc_dir.rglob("*.html")):
        text = page.read_text(encoding="utf-8")
        if HEADER_OLD in text:
            page.write_text(text.replace(HEADER_OLD, new_h1), encoding="utf-8")
            changed += 1
    return changed


def default_home_url() -> str:
    """The main documentation site: the repo's GitHub Pages root, from the origin remote.

    github.com/<owner>/<repo> publishes its Pages site at <owner>.github.io/<repo>/, and
    the doc-gen4 reference is attached one level under it (at /api). Override with --home-url."""
    url = subprocess.check_output(
        ["git", "remote", "get-url", "origin"], text=True, cwd=Path(__file__).resolve().parent
    ).strip()
    m = re.match(r"git@github\.com:(.+?)(?:\.git)?$", url) or re.match(
        r"https://github\.com/(.+?)(?:\.git)?$", url
    )
    if not m:
        sys.exit(f"cannot derive home URL from remote {url!r}; pass --home-url")
    owner, _, repo = m.group(1).partition("/")
    return f"https://{owner}.github.io/{repo}/"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("doc_dir", type=Path, help="doc-gen4 output dir (contains navbar.html)")
    parser.add_argument("--keep", default="Langlib", help="module kept visible at the top")
    parser.add_argument("--label", default=DEFAULT_LABEL, help="spoiler summary text")
    parser.add_argument("--open", action="store_true", dest="open_spoiler", help="render the spoilers expanded")
    parser.add_argument("--keep-general", action="store_true",
                        help='leave "General documentation" in place (do not move into the spoiler)')
    parser.add_argument("--home-url", default=None, help="header link target + logo base (default: repo Pages root)")
    parser.add_argument("--home-label", default=DEFAULT_HOME_LABEL, help="text shown beside the header logo")
    parser.add_argument("--no-header", action="store_true", help="do not rewrite the page header title")
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
        folded = fold_navbar(html, args.keep, args.label, args.open_spoiler, not args.keep_general)
        home_url = args.home_url or default_home_url()
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1

    if folded != html:
        navbar.write_text(folded, encoding="utf-8")
        extra = "" if args.keep_general else " (general docs nested)"
        print(f"folded navbar: kept {args.keep!r} at top, spoilered the rest{extra} -> {navbar}")
    else:
        print(f"navbar already folded (no change): {navbar}")

    if not args.no_header:
        n = rewrite_headers(args.doc_dir, home_url, args.home_label)
        print(f"rewrote header on {n} page(s) -> {args.home_label} logo linking {home_url}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
