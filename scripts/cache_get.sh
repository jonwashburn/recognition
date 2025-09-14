#!/usr/bin/env bash
set -euo pipefail

# Go to repo root (this script is in scripts/)
cd "$(dirname "$0")/.."

# Project env (elan, macOS SDKROOT)
# shellcheck disable=SC1090
source "$(dirname "$0")/env.sh"

echo "[cache_get] Tool versions:"
command -v elan >/dev/null 2>&1 && elan --version || echo "elan: not found"
command -v lean >/dev/null 2>&1 && lean --version || echo "lean: not found"
command -v lake >/dev/null 2>&1 && lake --version || echo "lake: not found"

echo "[cache_get] lake update"
lake update

echo "[cache_get] lake exe cache get"
lake exe cache get

echo "[cache_get] done"


