#!/usr/bin/env bash
set -euo pipefail

# Go to repo root (this script is in scripts/)
cd "$(dirname "$0")/.."

# Ensure elan env is loaded if available
if [ -f "$HOME/.elan/env" ]; then
  # shellcheck disable=SC1090
  source "$HOME/.elan/env"
fi

# Update deps to avoid network in build phase
lake update

# Build with logs
: "${OUT:=/tmp/recognition_build.out}"
: "${ERR:=/tmp/recognition_build.err}"

echo "[build] Building IndisputableMonolith (logs: $OUT, $ERR)"
if lake build IndisputableMonolith >"$OUT" 2>"$ERR"; then
  echo "[build] success"
else
  echo "[build] failed (see $ERR)"
  exit 1
fi
