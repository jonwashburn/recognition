#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  echo "lake not found; ensure Lean toolchain is installed"
  exit 1
fi

lake build IndisputableMonolith -j8


