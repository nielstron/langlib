from pathlib import Path
from tempfile import TemporaryDirectory
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import merge_aristotle_lean_changes as merge_script


class MergeAristotleLeanChangesTests(unittest.TestCase):
    def test_current_baseline_ref_returns_head_commit(self) -> None:
        old_git_output = merge_script.git_output
        try:
            merge_script.git_output = lambda *args, cwd=merge_script.REPO_ROOT: "deadbeef"
            self.assertEqual(merge_script.current_baseline_ref(), "deadbeef")
        finally:
            merge_script.git_output = old_git_output

    def test_parse_args_accepts_project_only(self) -> None:
        old_argv = sys.argv
        try:
            sys.argv = [
                "merge_aristotle_lean_changes.py",
                "cc20ef45-8127-4fe6-a66e-b2beab36d241",
            ]
            args = merge_script.parse_args()
        finally:
            sys.argv = old_argv
        self.assertEqual(args.project, "cc20ef45-8127-4fe6-a66e-b2beab36d241")

    def test_overwrite_with_output_replaces_repo_file(self) -> None:
        with TemporaryDirectory() as tmpdir_name:
            tmpdir = Path(tmpdir_name)
            repo_root = tmpdir / "repo"
            output_root = tmpdir / "output"
            relative_path = Path("src/Foo.lean")
            repo_file = repo_root / relative_path
            output_file = output_root / relative_path
            repo_file.parent.mkdir(parents=True)
            output_file.parent.mkdir(parents=True)
            repo_file.write_text("old\n")
            output_file.write_text("new\n")

            old_repo_root = merge_script.REPO_ROOT
            old_run = merge_script.run
            staged: list[list[str]] = []

            def fake_run(cmd: list[str], *, cwd: Path = merge_script.REPO_ROOT, check: bool = True):
                staged.append(cmd)
                return None

            try:
                merge_script.REPO_ROOT = repo_root
                merge_script.run = fake_run
                merge_script.overwrite_with_output(relative_path, output_root)
            finally:
                merge_script.REPO_ROOT = old_repo_root
                merge_script.run = old_run

            self.assertEqual(repo_file.read_text(), "new\n")
            self.assertEqual(staged, [["git", "add", "--", str(relative_path)]])

    def test_matching_historic_main_rev_returns_matching_older_commit(self) -> None:
        relative_path = Path("src/Foo.lean")
        old_git_file_text = merge_script.git_file_text
        old_git_file_history_revs = merge_script.git_file_history_revs
        try:
            merge_script.git_file_history_revs = lambda path, ref, cwd=merge_script.REPO_ROOT: [
                "newrev",
                "oldrev",
            ]
            merge_script.git_file_text = lambda rev, path, cwd=merge_script.REPO_ROOT: {
                "main": "current\n",
                "newrev": "current\n",
                "oldrev": "historic\n",
            }.get(rev)
            self.assertEqual(
                merge_script.matching_historic_main_rev(
                    relative_path,
                    "historic\n",
                    main_ref="feature-base",
                ),
                "oldrev",
            )
        finally:
            merge_script.git_file_text = old_git_file_text
            merge_script.git_file_history_revs = old_git_file_history_revs

    def test_matching_historic_main_rev_uses_provided_baseline_ref(self) -> None:
        relative_path = Path("src/Foo.lean")
        old_git_file_text = merge_script.git_file_text
        old_git_file_history_revs = merge_script.git_file_history_revs
        calls: list[tuple[str, Path]] = []
        try:
            merge_script.git_file_history_revs = lambda path, ref, cwd=merge_script.REPO_ROOT: ["oldrev"]

            def fake_git_file_text(rev, path, cwd=merge_script.REPO_ROOT):
                calls.append((rev, path))
                return {
                    "feature-base": "current\n",
                    "oldrev": "historic\n",
                }.get(rev)

            merge_script.git_file_text = fake_git_file_text
            self.assertEqual(
                merge_script.matching_historic_main_rev(
                    relative_path,
                    "historic\n",
                    main_ref="feature-base",
                ),
                "oldrev",
            )
        finally:
            merge_script.git_file_text = old_git_file_text
            merge_script.git_file_history_revs = old_git_file_history_revs

        self.assertEqual(calls[0], ("feature-base", relative_path))

    def test_stale_outdated_files_skips_when_input_matches_old_main(self) -> None:
        with TemporaryDirectory() as tmpdir_name:
            tmpdir = Path(tmpdir_name)
            input_root = tmpdir / "input"
            relative_path = Path("src/Foo.lean")
            (input_root / relative_path).parent.mkdir(parents=True)
            (input_root / relative_path).write_text("historic\n")

            old_matching_historic_main_rev = merge_script.matching_historic_main_rev
            try:
                merge_script.matching_historic_main_rev = (
                    lambda path, input_text, main_ref="main", cwd=merge_script.REPO_ROOT: "oldrev"
                )
                self.assertEqual(
                    merge_script.stale_outdated_files(
                        [relative_path],
                        input_root,
                    ),
                    {relative_path: "oldrev"},
                )
            finally:
                merge_script.matching_historic_main_rev = old_matching_historic_main_rev

    def test_files_to_overwrite_from_aristotle_includes_unchanged_followup_file(self) -> None:
        with TemporaryDirectory() as tmpdir_name:
            tmpdir = Path(tmpdir_name)
            input_root = tmpdir / "input"
            output_root = tmpdir / "output"
            relative_path = Path("src/PrimrecHelpers.lean")
            (input_root / relative_path).parent.mkdir(parents=True)
            (output_root / relative_path).parent.mkdir(parents=True)
            (input_root / relative_path).write_text("followup state\n")
            (output_root / relative_path).write_text("followup state\n")

            old_git_file_text = merge_script.git_file_text
            old_stale_outdated_files = merge_script.stale_outdated_files
            try:
                merge_script.git_file_text = (
                    lambda rev, path, cwd=merge_script.REPO_ROOT: "main state\n" if rev == "main" else None
                )
                merge_script.stale_outdated_files = (
                    lambda candidate_files, input_root, main_ref="main", cwd=merge_script.REPO_ROOT: {}
                )
                files_to_apply, stale_files = merge_script.files_to_overwrite_from_aristotle(
                    input_root,
                    output_root,
                )
            finally:
                merge_script.git_file_text = old_git_file_text
                merge_script.stale_outdated_files = old_stale_outdated_files

            self.assertEqual(files_to_apply, [relative_path])
            self.assertEqual(stale_files, {})

    def test_files_to_overwrite_from_aristotle_skips_stale_file(self) -> None:
        with TemporaryDirectory() as tmpdir_name:
            tmpdir = Path(tmpdir_name)
            input_root = tmpdir / "input"
            output_root = tmpdir / "output"
            relative_path = Path("src/Foo.lean")
            (input_root / relative_path).parent.mkdir(parents=True)
            (output_root / relative_path).parent.mkdir(parents=True)
            (input_root / relative_path).write_text("historic state\n")
            (output_root / relative_path).write_text("aristotle result\n")

            old_git_file_text = merge_script.git_file_text
            old_stale_outdated_files = merge_script.stale_outdated_files
            try:
                merge_script.git_file_text = (
                    lambda rev, path, cwd=merge_script.REPO_ROOT: "latest main\n" if rev == "main" else None
                )
                merge_script.stale_outdated_files = (
                    lambda candidate_files, input_root, main_ref="main", cwd=merge_script.REPO_ROOT: {
                        relative_path: "oldrev"
                    }
                )
                files_to_apply, stale_files = merge_script.files_to_overwrite_from_aristotle(
                    input_root,
                    output_root,
                )
            finally:
                merge_script.git_file_text = old_git_file_text
                merge_script.stale_outdated_files = old_stale_outdated_files

            self.assertEqual(files_to_apply, [])
            self.assertEqual(stale_files, {relative_path: "oldrev"})


if __name__ == "__main__":
    unittest.main()
