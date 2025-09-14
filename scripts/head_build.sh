#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Project env (elan, macOS SDKROOT)
# shellcheck disable=SC1090
source "$(dirname "$0")/env.sh"

: "${HEAD_LINES:=6000}"

cp IndisputableMonolith.lean IndisputableMonolith.full.lean
head -n "$HEAD_LINES" IndisputableMonolith.full.lean > IndisputableMonolith.lean

echo "[head_build] building first $HEAD_LINES lines..."
lake build IndisputableMonolith

echo "[head_build] restoring full file"
git checkout -- IndisputableMonolith.lean || cp IndisputableMonolith.full.lean IndisputableMonolith.lean

echo "[head_build] done"


