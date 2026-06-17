#!/usr/bin/env python3
from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class HubConfig:
    output: Path
    scan_root: Path | None
    module_prefix: str
    title: str
    summary_bullet: str
    modules: tuple[str, ...] = ()
    private_imports: tuple[str, ...] = ()
    excludes: tuple[Path, ...] = ()


REPO_ROOT = Path(__file__).resolve().parent.parent

DEFAULT_HUBS: dict[str, HubConfig] = {
    "langlib": HubConfig(
        output=REPO_ROOT / "src" / "Langlib.lean",
        scan_root=None,
        module_prefix="Langlib",
        title="Langlib Library",
        summary_bullet="Imports the language-class, grammar, automata, and utility developments.",
        modules=(
            "Langlib.Automata",
            "Langlib.Classes",
            "Langlib.Examples",
            "Langlib.Grammars",
            "Langlib.Utilities",
        ),
        private_imports=(
            "Mathlib.Data.EReal.Operations",
            "Mathlib.Data.Sym.Sym2.Init",
            "Mathlib.Topology.MetricSpace.Bounded",
        ),
    ),
    "automata": HubConfig(
        output=REPO_ROOT / "src" / "Langlib" / "Automata.lean",
        scan_root=REPO_ROOT / "src" / "Langlib" / "Automata",
        module_prefix="Langlib.Automata",
        title="Langlib Automata",
        summary_bullet="Imports the finite-state, pushdown, linear-bounded, and Turing-machine developments.",
    ),
    "classes": HubConfig(
        output=REPO_ROOT / "src" / "Langlib" / "Classes.lean",
        scan_root=REPO_ROOT / "src" / "Langlib" / "Classes",
        module_prefix="Langlib.Classes",
        title="Langlib Language Classes",
        summary_bullet="Imports the regular, context-free, indexed, recursive, recursively enumerable, and context-sensitive language-class developments.",
        private_imports=(
            "Mathlib.Data.EReal.Operations",
            "Mathlib.Data.Sym.Sym2.Init",
            "Mathlib.Topology.MetricSpace.Bounded",
        ),
    ),
    "examples": HubConfig(
        output=REPO_ROOT / "src" / "Langlib" / "Examples.lean",
        scan_root=REPO_ROOT / "src" / "Langlib" / "Examples",
        module_prefix="Langlib.Examples",
        title="Langlib Examples",
        summary_bullet="Imports the shared example languages and alphabets.",
        private_imports=("Mathlib.Tactic.Bound.Init",),
    ),
    "grammars": HubConfig(
        output=REPO_ROOT / "src" / "Langlib" / "Grammars.lean",
        scan_root=REPO_ROOT / "src" / "Langlib" / "Grammars",
        module_prefix="Langlib.Grammars",
        title="Langlib Grammars",
        summary_bullet="Imports the grammar definitions, transformations, and characterizations.",
    ),
    "utilities": HubConfig(
        output=REPO_ROOT / "src" / "Langlib" / "Utilities.lean",
        scan_root=REPO_ROOT / "src" / "Langlib" / "Utilities",
        module_prefix="Langlib.Utilities",
        title="Langlib Utilities",
        summary_bullet="Imports shared operations, predicates, tactics, and helper lemmas.",
    ),
    "tests": HubConfig(
        output=REPO_ROOT / "test" / "LanglibTest.lean",
        scan_root=REPO_ROOT / "test" / "LanglibTest",
        module_prefix="LanglibTest",
        title="Langlib Test Suite",
        summary_bullet="Imports the demo and theorem-checking test files.",
    ),
}


def lean_module_name(scan_root: Path, module_prefix: str, lean_file: Path) -> str:
    relative = lean_file.relative_to(scan_root).with_suffix("")
    parts = [module_prefix, *relative.parts]
    return ".".join(parts)


def collect_modules(config: HubConfig) -> list[str]:
    if config.modules:
        return list(config.modules)
    if config.scan_root is None:
        return []

    modules: list[str] = []
    excluded = {path.resolve() for path in config.excludes}
    for lean_file in sorted(config.scan_root.rglob("*.lean")):
        if lean_file.resolve() in excluded:
            continue
        modules.append(lean_module_name(config.scan_root, config.module_prefix, lean_file))
    return modules


def render_hub(config: HubConfig) -> str:
    modules = collect_modules(config)
    imports = "\n".join(
        [*(f"public import {module}" for module in modules), *(f"import {module}" for module in config.private_imports)]
    )
    return f"""module -- shake: keep-all

--! Auto-generated import hub for the {config.title.lower()}.
--  Run `scripts/generate_import_hub.py --hub {hub_name(config)}` to regenerate.

{imports}
@[expose]
public section

/-! # {config.title}

This file is the import hub for the {config.title.lower()}.

## Main declarations

- {config.summary_bullet}
-/
"""


def hub_name(config: HubConfig) -> str:
    for name, candidate in DEFAULT_HUBS.items():
        if candidate == config:
            return name
    return "custom"


def write_if_changed(path: Path, content: str) -> bool:
    if path.exists() and path.read_text() == content:
        return False
    path.write_text(content)
    return True


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--hub",
        choices=sorted(DEFAULT_HUBS),
        action="append",
        help="Named import hub to generate. Defaults to all known hubs.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Exit non-zero if any generated file is out of date.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    selected_names = args.hub or sorted(DEFAULT_HUBS)
    exit_code = 0

    for name in selected_names:
        config = DEFAULT_HUBS[name]
        rendered = render_hub(config)
        if args.check:
            on_disk = config.output.read_text() if config.output.exists() else None
            if on_disk != rendered:
                print(f"stale: {config.output.relative_to(REPO_ROOT)}")
                exit_code = 1
            continue

        changed = write_if_changed(config.output, rendered)
        verb = "updated" if changed else "unchanged"
        print(f"{verb}: {config.output.relative_to(REPO_ROOT)}")

    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
