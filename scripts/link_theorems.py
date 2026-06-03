#!/usr/bin/env python3
"""Link theorem/definition mentions in the docs to the doc-gen4 API reference.

Authors mention declarations by name (`` `memCode` ``) and do not hand-maintain links.
This script resolves every mention to its page in the published API reference
(`<api>/<Module/Path>.html#<FullName>`, e.g. `…/api/Langlib/Automata/FiniteState/
Definition.html#is_DFA`):

  * Bare code spans `` `name` `` whose content is a declaration in src/**/*.lean become
    ``[`name`](url)`` (first occurrence per page). Ambiguous names — declared in
    more than one file — are left untouched, since the target cannot be inferred.
  * Existing source links whose label is a known declaration are re-pointed, with the
    target file resolved from a `src/.../*.lean` path in the old URL when present, so
    re-running after edits refreshes the link.

The API URL is built structurally from the declaration's module (the source path maps
1:1 onto the doc-gen4 page: ``src/Langlib/X/Y.lean`` -> ``Langlib/X/Y.html``) and its
fully-qualified name (the page anchor), so no built API output is strictly needed.

Declarations the API reference does not document fall back to a commit-pinned GitHub
source permalink (``blob/<sha>/<path>#L<line>``). Pass ``--api-dir`` (a built doc-gen4
tree) to decide this exactly: each declaration links to the reference only if that page
actually carries its anchor, so private declarations *and* anything an outdated reference
is missing (e.g. a freshly added module) link to source instead. Without ``--api-dir``,
every declaration links to the API reference (unverified — intended for quick dry runs).

It does NOT touch prose. Docs should reference *theorems*, not files: bare file-path
references (``[`Classes/.../Foo.lean`](...)`` links, ``In `Classes/.../Foo.lean`:``
headers, inline ``path.lean`` spans) are reported as errors so they can be removed by
hand and kept out by a pre-commit hook. The theorem links carry the source location.

Declarations are indexed with namespace awareness, so both the short name (`memCode`) and
the fully-qualified name (`CFG_to_PDA.M`) resolve.

The transformed pages are written to a gitignored mirror (default docs/_linked/) — the
tracked sources are never modified, so running the linker does not pollute the repo. The
docs build (see .github/workflows/docs.yml) renders the mirror and points Jekyll at it.

Usage:
    python3 scripts/link_theorems.py                 # dry run: report linking + file refs
    python3 scripts/link_theorems.py --out DIR        # render the linked site source into DIR
    python3 scripts/link_theorems.py --check           # no writes; exit 1 if a file ref is found
    python3 scripts/link_theorems.py --api-dir DIR     # verify anchors vs a built doc-gen4 tree
    python3 scripts/link_theorems.py --api-base URL    # override the API reference root URL

Exit status is non-zero when any bare file reference is found (in every mode), so the same
invocation works as a pre-commit / CI gate.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from collections import defaultdict, namedtuple
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"
DOCS = REPO / "docs"

# Lean identifier characters. Names routinely use more than ASCII: a trailing `?`/`!`,
# subscripts (`grammarTest_computable₂`), primes, and Greek letters. doc-gen4 anchors carry
# these literally, so the index keys (and the doc-side scanner) must match them exactly.
_IDS = r"A-Za-z_À-ɏͰ-Ͽἀ-῿"  # identifier start
_IDC = _IDS + r"0-9'!?₀-ₜ"                      # identifier continuation
ID = rf"[{_IDS}][{_IDC}]*"        # single component (constructor / field)
QID = rf"[{_IDS}][{_IDC}.]*"      # dotted / qualified name

DECL_KW = r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)"
MODS = r"(?:(?:@\[[^\]]*\]|public|private|protected|scoped|local|noncomputable|partial|unsafe)\s+)*"
DECL_RE = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)*{MODS}{DECL_KW}\s+({QID})")
NS_RE = re.compile(rf"^\s*namespace\s+({QID})")
SEC_RE = re.compile(rf"^\s*section\b\s*({QID})?")
END_RE = re.compile(rf"^\s*end\b\s*({QID})?")

LINK_RE = re.compile(r"\[`?([^\]`]+)`?\]\((https://github\.com/[^)]+)\)")
SPAN_RE = re.compile(r"`([^`\n]+)`")


def _clean(name: str) -> str:
    """Strip a universe binder artifact: `def foo.{u}` / `structure Bar.{u}` capture a
    trailing dot (the `.` before `{`). No legitimate Lean name ends in a dot."""
    return name.rstrip(".")


SRCPATH_RE = re.compile(r"(src/Langlib/[^#)\s]+\.lean)")

# Bundle of link targets threaded through rendering: `api` is the doc-gen4 reference root
# and `gh`/`ref` build commit-pinned GitHub source permalinks (the fallback). `has_anchor`
# is an optional `(module, full_name) -> bool` probe against a built API tree: when present
# a declaration links to the API reference only if that page actually carries the anchor,
# and otherwise (private, or the API tree is outdated and lacks it) falls back to GitHub.
Links = namedtuple("Links", "api gh ref has_anchor")


def make_anchor_checker(api_dir: Path):
    """`(module, full_name) -> bool`: does <api_dir>/<module>.html define `id="full_name"`?

    Per-page anchor sets are cached; a missing page (an outdated API tree that predates a
    new module) reads as "no anchor", so its declarations fall back to GitHub source."""
    cache: dict[str, set[str] | None] = {}

    def has(module: str, full: str) -> bool:
        if module not in cache:
            f = api_dir / f"{module}.html"
            cache[module] = (
                set(re.findall(r'id="([^"]+)"', f.read_text(errors="replace")))
                if f.is_file() else None
            )
        ids = cache[module]
        return ids is not None and full in ids

    return has


def remote_slug() -> str:
    """The `owner/repo` of the `origin` remote."""
    url = subprocess.check_output(
        ["git", "-C", str(REPO), "remote", "get-url", "origin"], text=True
    ).strip()
    m = re.match(r"git@github\.com:(.+?)(?:\.git)?$", url) or re.match(
        r"https://github\.com/(.+?)(?:\.git)?$", url
    )
    if not m:
        sys.exit(f"cannot parse GitHub remote: {url}")
    return m.group(1)


def api_base() -> str:
    """Default API reference root: the project's GitHub Pages site, under /api.

    github.com/<owner>/<repo> serves its Pages site at <owner>.github.io/<repo>, and the
    docs deploy attaches the doc-gen4 output there under /api (see docs.yml)."""
    owner, _, repo = remote_slug().partition("/")
    return f"https://{owner}.github.io/{repo}/api"


def gh_base() -> str:
    return f"https://github.com/{remote_slug()}"


def head_sha() -> str:
    return subprocess.check_output(
        ["git", "-C", str(REPO), "rev-parse", "HEAD"], text=True
    ).strip()


BLOCK_RE = re.compile(rf"^(\s*)(?:@\[[^\]]*\]\s*)*{MODS}(structure|inductive|class)\s+({QID})")
CTOR_RE = re.compile(rf"\|\s*({ID})")            # constructors on an `inductive X | A | B` header
BODY_CTOR_RE = re.compile(rf"^\s*\|\s*({ID})")    # one constructor per body line; anchored so a
                                                  # mid-line `|` (a `|x|` in a comment, a `match`
                                                  # arm) is not mistaken for a constructor
FIELD_RE = re.compile(rf"^(\s+)({ID})\s*:(?!=)")


def build_index() -> dict[str, list[tuple[str, int, str]]]:
    """name -> sorted unique list of (relpath, line, full_name) where it is declared.

    Captures top-level declarations (def/theorem/lemma/...), and — so that docs can also
    link them — the constructors of inductive types and the fields of structures/classes,
    under both their short name and their fully-qualified `Type.member` name. The stored
    full name is the doc-gen4 page anchor; the relpath maps to its module page."""
    index: dict[str, set[tuple[str, int, str]]] = defaultdict(set)
    for path in sorted(SRC.rglob("*.lean")):
        rel = path.relative_to(REPO).as_posix()
        stack: list[tuple[str, str | None]] = []
        block: tuple[str, str, int] | None = None  # (kind, full name, indent)

        def add(name: str, owner: str | None, lineno: int):
            full = f"{owner}.{name}" if owner else name
            entry = (rel, lineno, full)
            index[name].add(entry)
            if owner:
                index[full].add(entry)

        for lineno, line in enumerate(path.read_text().splitlines(), start=1):
            stripped = line.strip()
            if block and stripped and (len(line) - len(line.lstrip())) <= block[2]:
                block = None  # dedent ends the structure/inductive body
            if NS_RE.match(line):
                stack.append(("ns", NS_RE.match(line).group(1)))
                continue
            if END_RE.match(line):
                if stack:
                    stack.pop()
                block = None
                continue
            if SEC_RE.match(line):
                stack.append(("sec", SEC_RE.match(line).group(1)))
                continue
            if block:  # inside a structure/inductive body: capture members
                if block[0] == "inductive":
                    if (cm := BODY_CTOR_RE.match(line)):
                        add(cm.group(1), block[1], lineno)
                elif (fm := FIELD_RE.match(line)):
                    add(fm.group(2), block[1], lineno)
                continue
            prefix = ".".join(n for k, n in stack if k == "ns" and n)
            if (m := BLOCK_RE.match(line)):
                name = _clean(m.group(3))
                full = f"{prefix}.{name}" if prefix else name
                add(name, prefix or None, lineno)
                if m.group(2) == "inductive":  # constructors on the header line itself
                    for c in CTOR_RE.findall(line[m.end():]):
                        add(c, full, lineno)
                block = (m.group(2), full, len(m.group(1)))
                continue
            if (m := DECL_RE.match(line)):
                add(_clean(m.group(1)), prefix or None, lineno)
    return {k: sorted(v) for k, v in index.items()}


def is_path_like(s: str) -> bool:
    """True for source file/directory references, not math like `N / D` or `L / R`."""
    s = s.strip()
    if not re.fullmatch(r"[\w.\-/]+", s):  # spaces / math symbols ⇒ not a path
        return False
    if s.endswith(".lean") or s.endswith("/"):
        return True
    if re.match(r"(?:src/)?(?:Classes|Automata|Grammars|Utilities)/", s):
        return True
    return s.count("/") >= 2


def linkable(name: str, index: dict) -> bool:
    """A token is linkable iff it names a declaration unambiguously and is not a bare
    single-letter variable. Multi-character declarations (CS, LBA, RE, CF, L4, ...) link;
    single letters (M, D, f, R, L, ...) — almost always bound variables — do not."""
    if name not in index or is_path_like(name):
        return False
    if len({e[0] for e in index[name]}) > 1:  # ambiguous: don't guess
        return False
    return len(name) >= 2


def resolve(name: str, index: dict, prefer_path: str | None) -> tuple[str, int, str] | None:
    locs = index.get(name)
    if not locs:
        return None
    if prefer_path:
        for entry in locs:
            if entry[0] == prefer_path:
                return entry
    if len({e[0] for e in locs}) > 1:
        return None
    return locs[0]


def url_for(rel: str, line: int, full: str, links: Links) -> str:
    """Link target for a declaration: its doc-gen4 page when the API reference carries it
    (``<api>/<Module/Path>.html#<FullName>`` — the source path maps 1:1 onto the module
    page, ``full`` is the anchor), otherwise a commit-pinned GitHub source permalink
    (``<gh>/blob/<sha>/<path>#L<line>``).

    With a built API tree (``links.has_anchor``) the choice is verified per declaration, so
    anything the reference lacks — private declarations, or an outdated tree missing a new
    module — falls back to GitHub. Without one, every declaration links to the API tree.

    Signature mirrors index entries so they splat straight in: ``url_for(*entry, links)``."""
    module = rel.removeprefix("src/").removesuffix(".lean")
    if links.has_anchor is None or links.has_anchor(module, full):
        return f"{links.api}/{module}.html#{full}"
    return f"{links.gh}/blob/{links.ref}/{rel}#L{line}"


def protect_blocks(body: str):
    """Yield (is_code, segment) splitting out fenced code blocks and $$ math blocks."""
    fence = re.compile(r"(^```.*?^```|^~~~.*?^~~~|^\$\$.*?^\$\$)", re.DOTALL | re.MULTILINE)
    pos = 0
    for m in fence.finditer(body):
        if m.start() > pos:
            yield (False, body[pos : m.start()])
        yield (True, m.group(0))
        pos = m.end()
    if pos < len(body):
        yield (False, body[pos:])


def find_file_refs(body: str):
    """Yield (lineno, kind, text) for every bare file reference outside code blocks."""
    base_line = body[: 0].count("\n")
    offset = 0
    for is_code, seg in protect_blocks(body):
        if not is_code:
            for m in LINK_RE.finditer(seg):
                if is_path_like(m.group(1)):
                    ln = body.count("\n", 0, offset + m.start()) + 1
                    yield (ln, "file-path link", m.group(0))
            for m in SPAN_RE.finditer(seg):
                s, e = m.span()
                if seg[max(0, s - 1) : s] == "[" and seg[e : e + 2] == "](":
                    continue  # link label, handled above
                if is_path_like(m.group(1)):
                    ln = body.count("\n", 0, offset + s) + 1
                    yield (ln, "inline file span", m.group(0))
        offset += len(seg)


IDENT_RE = re.compile(QID)


def _esc(s: str) -> str:
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def link_span(content: str, index, links):
    """Link a code span's content. Returns the replacement (with backticks) or None.

    A span that is exactly one declaration becomes a clean Markdown link; a span mixing
    declarations with other text (e.g. `is_RE R → is_Recursive R`) becomes an HTML
    <code> element with each known declaration wrapped in an anchor, so every mentioned
    theorem links to its definition. Intra-word underscores in identifiers are not
    Markdown emphasis, so this is safe inside kramdown."""
    toks = []
    for m in IDENT_RE.finditer(content):
        s, e, t = m.start(), m.end(), m.group(0)
        if linkable(t, index):
            toks.append((s, e, t))
        elif "." in t:  # dotted projection like `M.DecidesEveryInput`: link the member
            comp = t.rsplit(".", 1)[-1]
            if linkable(comp, index):
                toks.append((e - len(comp), e, comp))
    if not toks:
        return None
    stripped = content.strip()
    if len(toks) == 1 and stripped == toks[0][2]:
        name = stripped
        return f"[`{name}`]({url_for(*index[name][0], links)})"
    parts, last = [], 0
    for s, e, t in toks:
        parts.append(_esc(content[last:s]))
        parts.append(f'<a href="{url_for(*index[t][0], links)}">{t}</a>')
        last = e
    parts.append(_esc(content[last:]))
    return "<code>" + "".join(parts) + "</code>"


def link_segment(seg: str, index, links, stats, warnings) -> str:
    def on_link(m):
        label, url = m.group(1), m.group(2)
        core = label.strip()
        if is_path_like(core):
            return m.group(0)  # file ref: left for the error pass, not rewritten
        if core in index:
            hint = SRCPATH_RE.search(url)
            loc = resolve(core, index, hint.group(1) if hint else None)
            if loc:
                stats["repointed"] += 1
                return f"[`{core}`]({url_for(*loc, links)})"
            warnings.append(f"left as-is (ambiguous, no path hint): `{core}`")
        return m.group(0)

    seg = LINK_RE.sub(on_link, seg)

    out, last = [], 0
    for m in SPAN_RE.finditer(seg):
        s, e = m.span()
        if seg[max(0, s - 1) : s] == "[" and seg[e : e + 2] == "](":
            continue  # already a Markdown link label
        repl = link_span(m.group(1), index, links)
        if repl is None:
            continue
        out.append(seg[last:s])
        out.append(repl)
        last = e
        stats["linked"] += 1
    out.append(seg[last:])
    return "".join(out)


def process_doc(path: Path, index, links, stats, warnings) -> str | None:
    text = path.read_text()
    fm, body = "", text
    if text.startswith("---\n"):
        end = text.find("\n---\n", 4)
        if end != -1:
            fm, body = text[: end + 5], text[end + 5 :]
    pieces = [
        seg if is_code else link_segment(seg, index, links, stats, warnings)
        for is_code, seg in protect_blocks(body)
    ]
    new = fm + "".join(pieces)
    return new if new != text else None


# Build artifacts / caches under docs/ that must not be mirrored into the render dir.
SKIP_TOP = {"_site", ".jekyll-cache", ".bundle", ".sass-cache", "vendor"}


def doc_md_files():
    for path in sorted(DOCS.rglob("*.md")):
        parts = path.relative_to(DOCS).parts
        if parts and parts[0] in SKIP_TOP:
            continue
        yield path


def render(out: Path, index, links, stats, warnings):
    """Mirror the buildable docs tree into `out`, linking .md pages and copying the rest."""
    skip = SKIP_TOP | {out.name}
    if out.exists():
        shutil.rmtree(out)
    for src in sorted(DOCS.rglob("*")):
        parts = src.relative_to(DOCS).parts
        if parts and parts[0] in skip:
            continue
        dst = out / src.relative_to(DOCS)
        if src.is_dir():
            continue
        dst.parent.mkdir(parents=True, exist_ok=True)
        if src.suffix == ".md":
            new = process_doc(src, index, links, stats, warnings)
            dst.write_text(new if new is not None else src.read_text())
            stats["pages"] += 1
        else:
            shutil.copy2(src, dst)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", default=None, metavar="DIR",
                    help="render the linked site source into DIR (default: dry run)")
    ap.add_argument("--check", action="store_true", help="no render; only gate on file refs")
    ap.add_argument("--api-base", default=None, metavar="URL",
                    help="API reference root URL (default: the repo's GitHub Pages /api)")
    ap.add_argument("--api-dir", default=None, metavar="DIR",
                    help="built doc-gen4 tree to verify anchors against; declarations it "
                         "lacks (private / outdated) link to GitHub source instead")
    ap.add_argument("--ref", default=None,
                    help="git ref for GitHub source links (default: current HEAD sha)")
    args = ap.parse_args()

    links = Links(
        api=(args.api_base or api_base()).rstrip("/"),
        gh=gh_base(),
        ref=args.ref or head_sha(),
        has_anchor=make_anchor_checker(Path(args.api_dir)) if args.api_dir else None,
    )
    index = build_index()

    stats = defaultdict(int)
    warnings: list[str] = []
    file_refs: list[str] = []
    for path in doc_md_files():
        rel = path.relative_to(REPO).as_posix()
        text = path.read_text()
        body = text.split("\n---\n", 1)[1] if text.startswith("---\n") else text
        for ln, kind, snippet in find_file_refs(body):
            file_refs.append(f"{rel}:{ln}: {kind}: {snippet.strip()}")

    print(f"indexed {len(index)} declaration names from src/")
    mode = "verified against built API tree" if links.has_anchor else "structural (no --api-dir)"
    print(f"API base = {links.api}  [{mode}; fallback {links.gh}/blob/{links.ref[:9]}]")

    if args.out:
        out = Path(args.out)
        if not out.is_absolute():
            out = REPO / out
        render(out, index, links, stats, warnings)
        print(
            f"rendered {stats['pages']} pages -> {out.relative_to(REPO)} "
            f"(linked {stats['linked']} mentions, re-pointed {stats['repointed']} links)"
        )
    elif not args.check:
        # dry run: count what would be linked, without writing.
        for path in doc_md_files():
            process_doc(path, index, links, stats, warnings)
        print(
            f"would link {stats['linked']} bare mentions, re-point {stats['repointed']} links "
            f"(dry run — pass --out DIR to render)"
        )
    for w in sorted(set(warnings)):
        print(f"  warning: {w}")

    if file_refs:
        print(f"\nERROR: {len(file_refs)} bare file reference(s) found — reference theorems, not files:")
        for r in file_refs:
            print(f"  {r}")
        return 1
    print("\nno bare file references — OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
