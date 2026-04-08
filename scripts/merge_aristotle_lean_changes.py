#!/usr/bin/env python3
from __future__ import annotations

import argparse
import filecmp
import os
import shutil
import subprocess
import tarfile
import tempfile
import re
import urllib.request
from pathlib import Path
from urllib.parse import urlparse


API_BASE = "https://aristotle.harmonic.fun/api/v2"
REPO_ROOT = Path(__file__).resolve().parent.parent
PROJECT_ID_RE = re.compile(
    r"^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("project")
    parser.add_argument(
        "--branch",
        help="Branch to create. Defaults to aristotle/<project_id-prefix>.",
    )
    parser.add_argument(
        "--commit-message",
        default=None,
        help="Commit message to create after applying the Lean changes.",
    )
    return parser.parse_args()


def extract_project_id(project: str) -> str:
    if PROJECT_ID_RE.fullmatch(project):
        return project.lower()

    parsed = urlparse(project)
    path_parts = [part for part in parsed.path.split("/") if part]
    if len(path_parts) >= 3 and path_parts[-2] == "requests":
        candidate = path_parts[-1]
        if PROJECT_ID_RE.fullmatch(candidate):
            return candidate.lower()

    raise ValueError(f"could not extract Aristotle project id from: {project}")


def api_key() -> str:
    return os.environ["ARISTOTLE_API_KEY"]


def run(cmd: list[str], *, cwd: Path = REPO_ROOT, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, check=check, text=True, capture_output=True)


def git_output(*args: str, cwd: Path = REPO_ROOT) -> str:
    return run(["git", *args], cwd=cwd).stdout.strip()


def download_project_artifact(project_id: str, kind: str, destination: Path) -> None:
    request = urllib.request.Request(
        f"{API_BASE}/project/{project_id}/{kind}",
        headers={"X-API-Key": api_key()},
    )
    with urllib.request.urlopen(request) as response, destination.open("wb") as output:
        shutil.copyfileobj(response, output)


def extract_tarball(archive: Path, destination: Path) -> Path:
    with tarfile.open(archive, "r:gz") as tar:
        tar.extractall(destination)
    children = [path for path in destination.iterdir()]
    if len(children) == 1 and children[0].is_dir():
        return children[0]
    return destination


def lean_files(root: Path) -> set[Path]:
    return {path.relative_to(root) for path in root.rglob("*.lean")}


def changed_lean_files(input_root: Path, output_root: Path) -> list[Path]:
    changed: list[Path] = []
    for relative_path in sorted(lean_files(input_root) | lean_files(output_root)):
        input_path = input_root / relative_path
        output_path = output_root / relative_path
        if not input_path.exists() or not output_path.exists():
            changed.append(relative_path)
            continue
        if not filecmp.cmp(input_path, output_path, shallow=False):
            changed.append(relative_path)
    return changed


def ensure_clean_worktree() -> None:
    status = git_output("status", "--short")
    if status:
        raise RuntimeError("worktree must be clean before importing Aristotle changes")


def ensure_branch_absent(branch: str) -> None:
    result = subprocess.run(
        ["git", "show-ref", "--verify", "--quiet", f"refs/heads/{branch}"],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode == 0:
        raise RuntimeError(f"branch already exists: {branch}")


def create_branch(branch: str) -> None:
    run(["git", "switch", "-c", branch])


def read_text(path: Path) -> str:
    return path.read_text() if path.exists() else ""


def merge_file(current_path: Path, base_path: Path, other_path: Path) -> tuple[str, bool]:
    with tempfile.TemporaryDirectory(prefix="aristotle-merge-file-") as tmpdir_name:
        tmpdir = Path(tmpdir_name)
        current_tmp = tmpdir / "current.lean"
        base_tmp = tmpdir / "base.lean"
        other_tmp = tmpdir / "other.lean"
        merged_tmp = tmpdir / "merged.lean"

        current_tmp.write_text(read_text(current_path))
        base_tmp.write_text(read_text(base_path))
        other_tmp.write_text(read_text(other_path))

        with merged_tmp.open("w") as merged_output:
            result = subprocess.run(
                ["git", "merge-file", "-p", str(current_tmp), str(base_tmp), str(other_tmp)],
                cwd=REPO_ROOT,
                check=False,
                text=True,
                stdout=merged_output,
                stderr=subprocess.PIPE,
            )
        merged_text = merged_tmp.read_text()
        return merged_text, result.returncode == 1


def apply_changed_file(relative_path: Path, input_root: Path, output_root: Path) -> bool:
    current_path = REPO_ROOT / relative_path
    base_path = input_root / relative_path
    other_path = output_root / relative_path
    merged_text, conflicted = merge_file(current_path, base_path, other_path)

    if other_path.exists() or merged_text:
        current_path.parent.mkdir(parents=True, exist_ok=True)
        current_path.write_text(merged_text)
        run(["git", "add", "--", str(relative_path)])
    elif current_path.exists():
        run(["git", "rm", "-f", "--", str(relative_path)])

    return conflicted


def commit_changes(project_id: str, changed_files: list[Path], commit_message: str | None) -> None:
    if not changed_files:
        return
    if commit_message is None:
        commit_message = f"Import Lean changes from Aristotle project {project_id}"
    run(["git", "commit", "-m", commit_message])


def main() -> int:
    args = parse_args()
    project_id = extract_project_id(args.project)
    branch = args.branch or f"aristotle/{project_id[:8]}"

    ensure_clean_worktree()
    ensure_branch_absent(branch)

    with tempfile.TemporaryDirectory(prefix="aristotle-import-") as tmpdir_name:
        tmpdir = Path(tmpdir_name)
        input_tar = tmpdir / "input.tar.gz"
        output_tar = tmpdir / "result.tar.gz"
        input_dir = tmpdir / "input"
        output_dir = tmpdir / "output"

        download_project_artifact(project_id, "input", input_tar)
        download_project_artifact(project_id, "result", output_tar)

        input_root = extract_tarball(input_tar, input_dir)
        output_root = extract_tarball(output_tar, output_dir)
        changed_files = changed_lean_files(input_root, output_root)

        create_branch(branch)
        conflicted_files = [
            relative_path
            for relative_path in changed_files
            if apply_changed_file(relative_path, input_root, output_root)
        ]

    commit_changes(project_id, changed_files, args.commit_message)

    print(f"Created branch: {branch}")
    if changed_files:
        print(f"Applied {len(changed_files)} Lean file(s).")
    else:
        print("No Lean file changes found.")
    if conflicted_files:
        print("Conflicts:")
        for relative_path in conflicted_files:
            print(relative_path)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
