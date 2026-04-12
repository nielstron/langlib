#!/usr/bin/env python3
"""
find_unused.py — classify and optionally remove lemmas/theorems in a Lean 4 project.

Declarations are grouped into three categories:

  (a) Shown results — public `theorem` declarations with NO references
      elsewhere (standalone results, not used as helpers).  Not listed under
      `## Main declarations` in their file's doc comment.  Consider adding them.

  (b) Possibly unnecessary — non-private `lemma` declarations with NO
      references anywhere in the scanned tree and not in the module doc.
      Removable with `--remove --force`.

  (c) Definitely remove — private lemmas/theorems with no references.
      Removable with `--remove`.

Lemmas with auto-use attributes (@[simp], @[ext], @[instance], @[aesop], …)
are excluded from (b) and (c) because they are used implicitly by tactics.
Lemmas listed in `## Main declarations` are excluded from all categories.

Usage:
  python3 scripts/find_unused.py [options] [src_dir]

  --remove         Remove all (c) declarations from source files in-place.
  --remove --force Also remove (b) declarations (implies --remove).
  --dry-run        With --remove: print what would be removed, but don't write.
"""

from __future__ import annotations

import argparse
import bisect
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants / compiled patterns
# ---------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parent.parent

_ID_START = r"[a-zA-Z_\u03b1-\u03c9\u0391-\u03a9]"
_ID_CONT  = r"[a-zA-Z0-9_'\u03b1-\u03c9\u0391-\u03a9\u2080-\u2089\u2090-\u2099]"
IDENT_RE  = re.compile(_ID_START + _ID_CONT + r"*")

DECL_RE = re.compile(
    r"^[ \t]*"
    r"(?:(?:private|protected|noncomputable|scoped)\s+)*"
    r"(lemma|theorem)\s+"
    r"(" + _ID_START + _ID_CONT + r"*)",
    re.MULTILINE,
)

ATTR_BLOCK_RE = re.compile(r"@\[([^\]]*)\]")

AUTO_ATTRS: frozenset[str] = frozenset({
    "simp", "ext", "instance", "aesop", "gcongr",
    "norm_num", "norm_cast", "fun_prop", "positivity",
    "continuity", "measurability", "push_neg", "simp_intro",
})

MODULE_DOC_RE    = re.compile(r"/-!(.*?)-/", re.DOTALL)
MAIN_SECTION_RE  = re.compile(r"##\s*Main declarations(.*?)(?=##|\Z)", re.DOTALL | re.IGNORECASE)
DECL_ITEM_RE     = re.compile(r"[-*•]\s*`([^`]+)`")

# Lines that syntactically "attach" to the declaration that follows them
_ATTR_LINE_RE       = re.compile(r"^\s*@\[")
_SETOPTION_LINE_RE  = re.compile(r"^\s*set_option\s+\S+.*\bin\b\s*$")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _char_to_line(newline_positions: list[int], offset: int) -> int:
    lo, hi = 0, len(newline_positions) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if newline_positions[mid] <= offset:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


def _is_attached_prefix(line: str) -> bool:
    """True if this line syntactically belongs to the declaration below it."""
    return bool(_ATTR_LINE_RE.match(line) or _SETOPTION_LINE_RE.match(line))


def _is_block_comment_end(line: str) -> bool:
    s = line.strip()
    return s == "-/" or (s.endswith("-/") and "/-" not in s)


def _is_block_comment_start(line: str) -> bool:
    s = line.strip()
    return s.startswith("/-") and not s.startswith("/-!")


# ---------------------------------------------------------------------------
# File parsing
# ---------------------------------------------------------------------------

def extract_main_decls(content: str) -> set[str]:
    doc = MODULE_DOC_RE.search(content)
    if not doc:
        return set()
    section = MAIN_SECTION_RE.search(doc.group(1))
    if not section:
        return set()
    return {m.group(1).strip() for m in DECL_ITEM_RE.finditer(section.group(1))}


def extract_declarations(content: str, filepath: str) -> list[dict]:
    lines = content.splitlines(keepends=True)
    newline_pos: list[int] = [0]
    for line in lines:
        newline_pos.append(newline_pos[-1] + len(line))

    attr_by_line: dict[int, set[str]] = defaultdict(set)
    for m in ATTR_BLOCK_RE.finditer(content):
        ln = _char_to_line(newline_pos, m.start())
        for attr in m.group(1).split(","):
            attr_by_line[ln].add(attr.strip())

    decls: list[dict] = []
    for m in DECL_RE.finditer(content):
        keyword = m.group(1)
        name = m.group(2)
        ln   = _char_to_line(newline_pos, m.start())
        is_private   = "private" in m.group(0)
        has_auto_attr = any(
            AUTO_ATTRS & attr_by_line.get(k, set())
            for k in range(max(1, ln - 4), ln + 1)
        )
        decls.append({
            "name":          name,
            "keyword":       keyword,
            "line":          ln,       # 1-based
            "is_private":    is_private,
            "has_auto_attr": has_auto_attr,
            "file":          filepath,
        })
    return decls


def tokenize(content: str) -> list[str]:
    return IDENT_RE.findall(content)


# ---------------------------------------------------------------------------
# Classification
# ---------------------------------------------------------------------------

def classify(src_dir: Path) -> tuple[list, list, list, list, dict, dict]:
    """
    Returns (all_decls, cat_a, cat_b, cat_c, file_contents, global_count).
      cat_a  — public, used, not in module doc
      cat_b  — public, unused, not in module doc
      cat_c  — private, unused
    """
    lean_files = sorted(src_dir.rglob("*.lean"))
    if not lean_files:
        print(f"No .lean files found under {src_dir}", file=sys.stderr)
        return [], [], [], [], {}, Counter()

    print(f"Scanning {len(lean_files)} files …", file=sys.stderr)

    all_decls:          list[dict]          = []
    file_main_decls:    dict[str, set[str]] = {}
    file_token_count:   dict[str, Counter]  = {}
    global_token_count: Counter             = Counter()
    file_contents:      dict[str, str]      = {}

    for f in lean_files:
        try:
            content = f.read_text(encoding="utf-8")
        except Exception as exc:
            print(f"  [warn] cannot read {f}: {exc}", file=sys.stderr)
            continue
        key = str(f)
        file_main_decls[key]  = extract_main_decls(content)
        decls                 = extract_declarations(content, key)
        all_decls.extend(decls)
        file_contents[key]    = content
        tokens                = tokenize(content)
        counter               = Counter(tokens)
        file_token_count[key] = counter
        global_token_count.update(tokens)

    print(f"Found {len(all_decls)} lemmas/theorems.", file=sys.stderr)

    cat_a: list[dict] = []
    cat_b: list[dict] = []
    cat_c: list[dict] = []

    for decl in all_decls:
        name          = decl["name"]
        key           = decl["file"]
        in_main_decls = name in file_main_decls.get(key, set())

        if in_main_decls:
            continue

        count = (
            file_token_count.get(key, Counter())[name]
            if decl["is_private"]
            else global_token_count[name]
        )
        is_unused = count <= 1

        if decl["is_private"]:
            if is_unused and not decl["has_auto_attr"]:
                cat_c.append(decl)
        else:
            if is_unused and not decl["has_auto_attr"]:
                if decl["keyword"] == "theorem":
                    cat_a.append(decl)
                else:
                    cat_b.append(decl)

    return all_decls, cat_a, cat_b, cat_c, file_contents, global_token_count


# ---------------------------------------------------------------------------
# Removal
# ---------------------------------------------------------------------------

def _removal_span(lines: list[str], decl_line_0: int,
                  all_decl_lines_0: list[int]) -> tuple[int, int]:
    """
    Return (start, end) inclusive 0-based line indices to delete for the
    declaration at decl_line_0.

    Walks backward to include:
      • Consecutive @[...] and 'set_option … in' lines (no blank lines between)
      • An optional preceding /- … -/ block comment (with ≤1 blank line gap)

    Walks forward to the line before the next declaration (or end of file),
    then trims trailing blank lines.
    """
    start = decl_line_0

    # ── backward pass 1: attached prefix lines ──────────────────────────────
    i = decl_line_0 - 1
    while i >= 0:
        stripped = lines[i].strip()
        if not stripped:
            break
        if _is_attached_prefix(lines[i]):
            start = i
            i -= 1
        else:
            break

    # ── backward pass 2: optional preceding block comment ───────────────────
    j = start - 1
    # allow one blank line between comment and declaration/attributes
    if j >= 0 and not lines[j].strip():
        j -= 1
    if j >= 0 and (_is_block_comment_end(lines[j]) or _is_block_comment_start(lines[j])):
        # found a closing -/ (or a one-liner /- ... -/)
        # scan upward to find the matching /-
        if _is_block_comment_start(lines[j]):
            # single-line block comment
            start = j
        else:
            k = j - 1
            while k >= 0 and not _is_block_comment_start(lines[k]):
                k -= 1
            if k >= 0 and _is_block_comment_start(lines[k]):
                start = k

    # ── forward: find end ────────────────────────────────────────────────────
    idx = bisect.bisect_right(all_decl_lines_0, decl_line_0)
    if idx < len(all_decl_lines_0):
        next_decl = all_decl_lines_0[idx]
        # walk backward from next_decl to skip its own prefix lines
        next_start = next_decl
        j = next_decl - 1
        while j >= 0:
            if not lines[j].strip():
                break
            if _is_attached_prefix(lines[j]):
                next_start = j
                j -= 1
            else:
                break
        end = next_start - 1
    else:
        end = len(lines) - 1

    # trim trailing blank lines within our block
    while end > start and not lines[end].strip():
        end -= 1

    return start, end


def remove_declarations(decls_to_remove: list[dict],
                        file_contents: dict[str, str],
                        dry_run: bool = False) -> dict[str, str]:
    """
    Remove declarations from their files.  Returns {filepath: new_content}.
    If dry_run, prints spans but does not modify anything.
    """
    by_file: dict[str, list[dict]] = defaultdict(list)
    for d in decls_to_remove:
        by_file[d["file"]].append(d)

    results: dict[str, str] = {}
    cwd = Path.cwd()

    for filepath, decls in sorted(by_file.items()):
        content = file_contents.get(filepath, "")
        lines   = content.splitlines(keepends=False)

        # 0-based sorted line numbers of ALL declarations in this file
        all_decl_lines_0 = sorted(
            d["line"] - 1 for d in extract_declarations(content, filepath)
        )

        lines_to_remove: set[int] = set()
        for d in decls:
            decl_line_0 = d["line"] - 1
            start, end  = _removal_span(lines, decl_line_0, all_decl_lines_0)

            if dry_run:
                try:
                    rel = Path(filepath).relative_to(cwd)
                except ValueError:
                    rel = Path(filepath)
                print(f"  would remove {rel} lines {start+1}–{end+1}: {d['name']}")

            for i in range(start, end + 1):
                lines_to_remove.add(i)

        new_lines    = [ln for i, ln in enumerate(lines) if i not in lines_to_remove]
        results[filepath] = "\n".join(new_lines) + "\n"

    return results


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------

def _rel(path: str) -> Path:
    try:
        return Path(path).relative_to(Path.cwd())
    except ValueError:
        return Path(path)


def _print_group(decls: list[dict]) -> None:
    if not decls:
        print("  (none)")
        return
    by_file: dict[str, list[dict]] = defaultdict(list)
    for d in decls:
        by_file[d["file"]].append(d)
    for key in sorted(by_file):
        print(f"  {_rel(key)}")
        for d in sorted(by_file[key], key=lambda x: x["line"]):
            tags = []
            if d.get("is_private"):
                tags.append("private")
            tag_str = f"  [{', '.join(tags)}]" if tags else ""
            print(f"    {d['line']:5d}  {d['name']}{tag_str}")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "src_dir", nargs="?", default=str(REPO_ROOT / "src"),
        help="Directory to scan (default: %(default)s)",
    )
    parser.add_argument(
        "--remove", action="store_true",
        help="Remove category (c) declarations in-place.",
    )
    parser.add_argument(
        "--force", "-f", action="store_true",
        help="Also remove category (b) declarations (requires --remove).",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="With --remove: show what would be deleted without writing.",
    )
    args = parser.parse_args()

    if args.force and not args.remove:
        parser.error("--force requires --remove")

    src_dir = Path(args.src_dir)
    _, cat_a, cat_b, cat_c, file_contents, _ = classify(src_dir)

    W = 64
    print(f"\n{'═' * W}")
    print("(a) Public theorems with no references (shown results)")
    print("    (Consider adding to ## Main declarations in the module doc)")
    print(f"{'─' * W}")
    _print_group(cat_a)

    print(f"\n{'═' * W}")
    print("(b) Non-private lemmas with no references (possibly unnecessary)")
    print("    Remove with:  --remove --force")
    print(f"{'─' * W}")
    _print_group(cat_b)

    print(f"\n{'═' * W}")
    print("(c) Private lemmas with no references")
    print("    Remove with:  --remove")
    print(f"{'─' * W}")
    _print_group(cat_c)

    print(f"\n{'─' * W}")
    print(
        f"(a) {len(cat_a):4d} theorems not in doc  │"
        f"  (b) {len(cat_b):4d} possibly unnecessary  │"
        f"  (c) {len(cat_c):4d} to remove"
    )

    # ── removal ────────────────────────────────────────────────────────────
    to_remove: list[dict] = []
    if args.remove:
        to_remove.extend(cat_c)
    if args.force:
        to_remove.extend(cat_b)

    if not to_remove:
        return

    label = "Dry-run:" if args.dry_run else "Removing"
    print(f"\n{label} {len(to_remove)} declaration(s) …")

    new_contents = remove_declarations(to_remove, file_contents, dry_run=args.dry_run)

    if not args.dry_run:
        for filepath, content in sorted(new_contents.items()):
            Path(filepath).write_text(content, encoding="utf-8")
            print(f"  updated {_rel(filepath)}")
        print("Done.")


if __name__ == "__main__":
    main()
