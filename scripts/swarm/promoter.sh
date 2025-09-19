#!/usr/bin/env bash
set -euo pipefail

# Promoter: move green WIP files to final location, trim monolith, update PORTMAP, keep Core green.

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT_DIR"

if [[ $# -lt 2 ]]; then
  echo "Usage: $0 WIP/IndisputableMonolith/<Module>.lean IndisputableMonolith/<Module>.lean" >&2
  exit 1
fi

SRC="$1"
DST="$2"

if [[ ! -f "$SRC" ]]; then
  echo "WIP source not found: $SRC" >&2
  exit 1
fi

echo "[promoter] Checking standalone: $SRC"
lake env lean --root=. --json "$SRC" | cat

echo "[promoter] Moving file to $DST"
mkdir -p "$(dirname "$DST")"
git mv -f "$SRC" "$DST" || { mv "$SRC" "$DST"; git add -A; }

echo "[promoter] Trimming monolith comment (manual step may be required)."
# This script leaves trimming to agents or a separate tool to avoid accidental deletions.

echo "[promoter] Building core"
lake build IndisputableMonolith.Core | cat

echo "[promoter] Updating PORTMAP.json (manual or agent-driven)"

echo "[promoter] Committing"
git add -A
git commit -m "Promote shard: ${DST#IndisputableMonolith/} (core green)" | cat || true

echo "[promoter] Done."


