#!/usr/bin/env bash
set -euo pipefail

# Verify all WIP Lean files compile standalone (JSON mode), ignoring macOS AppleDouble files.

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT_DIR"

shopt -s globstar nullglob

found_any=false
for f in WIP/IndisputableMonolith/**/*.lean WIP/IndisputableMonolith/*.lean; do
  base="$(basename "$f")"
  case "$base" in
    ._*) continue;;
  esac
  if [[ -f "$f" ]]; then
    found_any=true
    echo "[verify_wip] Checking: $f"
    lake env lean --root=. --json "$f" | cat
  fi
done

if [[ "$found_any" == false ]]; then
  echo "[verify_wip] No WIP files found under WIP/IndisputableMonolith/."
fi

echo "[verify_wip] Done."


