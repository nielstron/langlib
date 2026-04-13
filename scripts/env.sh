aris() {
  uv run aristotle submit "$@" --project-dir .
}

amerge() {
  uv run scripts/merge_aristotle_lean_changes.py "$@"
}
