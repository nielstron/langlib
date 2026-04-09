#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
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


def project_metadata(project_id: str) -> dict[str, object]:
    request = urllib.request.Request(
        f"{API_BASE}/project/{project_id}",
        headers={"X-API-Key": api_key()},
    )
    with urllib.request.urlopen(request) as response:
        return json.load(response)


def extract_tarball(archive: Path, destination: Path) -> Path:
    with tarfile.open(archive, "r:gz") as tar:
        tar.extractall(destination)
    children = [path for path in destination.iterdir()]
    if len(children) == 1 and children[0].is_dir():
        return children[0]
    return destination


def lean_files(root: Path) -> set[Path]:
    return {path.relative_to(root) for path in root.rglob("*.lean")}


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


def regenerate_import_hubs() -> None:
    run(["python3", "scripts/generate_import_hub.py", "--hub", "langlib"])
    run(["python3", "scripts/generate_import_hub.py", "--hub", "tests"])


def read_text(path: Path) -> str:
    return path.read_text() if path.exists() else ""


def overwrite_with_output(relative_path: Path, output_root: Path) -> None:
    current_path = REPO_ROOT / relative_path
    output_path = output_root / relative_path
    if output_path.exists():
        current_path.parent.mkdir(parents=True, exist_ok=True)
        current_path.write_text(output_path.read_text())
        run(["git", "add", "--", str(relative_path)])
    elif current_path.exists():
        run(["git", "rm", "-f", "--", str(relative_path)])


def git_file_text(rev: str, relative_path: Path, *, cwd: Path = REPO_ROOT) -> str | None:
    result = subprocess.run(
        ["git", "show", f"{rev}:{relative_path.as_posix()}"],
        cwd=cwd,
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        return None
    return result.stdout


def git_file_history_revs(relative_path: Path, ref: str, *, cwd: Path = REPO_ROOT) -> list[str]:
    output = git_output("log", "--format=%H", ref, "--", str(relative_path), cwd=cwd)
    return [line for line in output.splitlines() if line]


def matching_historic_main_rev(
    relative_path: Path,
    input_text: str,
    *,
    main_ref: str = "main",
    cwd: Path = REPO_ROOT,
) -> str | None:
    latest_text = git_file_text(main_ref, relative_path, cwd=cwd)
    if latest_text == input_text:
        return None
    for rev in git_file_history_revs(relative_path, main_ref, cwd=cwd):
        if git_file_text(rev, relative_path, cwd=cwd) == input_text:
            return rev
    return None


def stale_outdated_files(
    candidate_files: list[Path],
    input_root: Path,
    *,
    main_ref: str = "main",
    cwd: Path = REPO_ROOT,
) -> dict[Path, str]:
    stale: dict[Path, str] = {}
    for relative_path in candidate_files:
        input_path = input_root / relative_path
        if not input_path.exists():
            continue
        input_text = read_text(input_path)
        latest_text = git_file_text(main_ref, relative_path, cwd=cwd)
        if latest_text == input_text:
            continue
        rev = matching_historic_main_rev(relative_path, input_text, main_ref=main_ref, cwd=cwd)
        if rev is not None:
            stale[relative_path] = rev
    return stale


def files_to_overwrite_from_aristotle(
    input_root: Path,
    output_root: Path,
    *,
    main_ref: str = "main",
    cwd: Path = REPO_ROOT,
) -> tuple[list[Path], dict[Path, str]]:
    candidate_files: list[Path] = []
    for relative_path in sorted(lean_files(input_root) | lean_files(output_root)):
        input_text = read_text(input_root / relative_path) if (input_root / relative_path).exists() else None
        output_text = read_text(output_root / relative_path) if (output_root / relative_path).exists() else None
        latest_text = git_file_text(main_ref, relative_path, cwd=cwd)
        if input_text == latest_text and output_text == latest_text:
            continue
        candidate_files.append(relative_path)
    stale_files = stale_outdated_files(candidate_files, input_root, main_ref=main_ref, cwd=cwd)
    files_to_apply = [path for path in candidate_files if path not in stale_files]
    return files_to_apply, stale_files


def default_commit_message(project_id: str, prompt: str | None) -> str:
    if prompt:
        normalized = " ".join(prompt.split())
        if normalized:
            return normalized
    return f"Import Lean changes from Aristotle project {project_id}"


def print_skipped_stale_files(stale_files: dict[Path, str]) -> None:
    if not stale_files:
        return
    print("Skipped stale Aristotle changes:")
    for relative_path, rev in stale_files.items():
        print(f"{relative_path} (matches historic main state at {rev[:12]})")


def commit_changes(
    project_id: str, prompt: str | None, changed_files: list[Path], commit_message: str | None
) -> None:
    if not changed_files:
        return
    if commit_message is None:
        commit_message = default_commit_message(project_id, prompt)
    run(["git", "commit", "-m", commit_message])


def main() -> int:
    args = parse_args()
    project_id = extract_project_id(args.project)
    metadata = project_metadata(project_id)
    prompt = metadata.get("input_prompt")
    if prompt is not None and not isinstance(prompt, str):
        raise TypeError(f"expected input_prompt to be a string, got {type(prompt).__name__}")
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
        changed_files, stale_files = files_to_overwrite_from_aristotle(input_root, output_root)

        create_branch(branch)
        conflicted_files: list[Path] = []
        for relative_path in changed_files:
            overwrite_with_output(relative_path, output_root)
        regenerate_import_hubs()
        run(["git", "add", "--", "src/Langlib.lean", "test/LanglibTest.lean"])

    commit_changes(project_id, prompt, changed_files, args.commit_message)

    print(f"Created branch: {branch}")
    print_skipped_stale_files(stale_files)
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
