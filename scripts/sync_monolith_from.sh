#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 /absolute/path/to/IndisputableMonolith.lean" >&2
  exit 1
fi

SRC="$1"

if [[ ! -f "$SRC" ]]; then
  echo "Source file not found: $SRC" >&2
  exit 1
fi

if ! grep -q "namespace IndisputableMonolith" "$SRC"; then
  echo "Warning: source does not look like the monolith (namespace not found)" >&2
fi

REPO_ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
DEST="$REPO_ROOT_DIR/IndisputableMonolith.lean"

cp "$SRC" "$DEST"
echo "Copied $SRC -> $DEST"

if command -v git >/dev/null 2>&1; then
  cd "$REPO_ROOT_DIR"
  git add IndisputableMonolith.lean
  git commit -m "Sync monolith from $SRC"
  echo "Committed sync. You can push with: git push"
fi


