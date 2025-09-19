#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT_DIR"

usage() {
  echo "Usage: $0 --concurrency N --queue scripts/swarm/queue.json"
}

CONCURRENCY=5
QUEUE="scripts/swarm/queue.json"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --concurrency) CONCURRENCY="$2"; shift 2;;
    --queue) QUEUE="$2"; shift 2;;
    *) usage; exit 1;;
  esac
done

if [[ ! -f "$QUEUE" ]]; then
  echo "Queue file not found: $QUEUE" >&2
  exit 1
fi

echo "[master] Using queue: $QUEUE with concurrency=$CONCURRENCY"

python3 scripts/swarm/enqueue_blocks.py --source IndisputableMonolith.lean --out "$QUEUE" | cat || true

echo "[master] Verifying WIP files (if any) before starting..."
scripts/swarm/verify_wip.sh | cat

echo "[master] To proceed, launch agents with the provided prompt and point them at jobs from $QUEUE."
echo "[master] When jobs return green WIP files, the promoter will handle promotion serially."


