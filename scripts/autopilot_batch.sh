#!/bin/bash
# Batch autopilot: iterate Core build and all WIP files quickly.
# Usage: ./scripts/autopilot_batch.sh [num_iterations]

set -euo pipefail
NUM_ITERATIONS=${1:-3}

for i in $(seq 1 "$NUM_ITERATIONS"); do
  echo "=== [autopilot batch] iteration $i / $NUM_ITERATIONS: $(date -uIs) ==="
  echo "-- progress"
  ./scripts/progress.sh || true

  echo "-- building core umbrella"
  lake build IndisputableMonolith.Core | cat || true

  echo "-- checking all WIP files (standalone)"
  while IFS= read -r -d '' f; do
    # Skip macOS dot-underscore files
    if [[ "$(basename "$f")" == ._* ]]; then continue; fi
    echo "   * WIP: $f"
    lake env lean --root=. --json "$f" | cat || true
  done < <(find WIP -type f -name "*.lean" -print0 2>/dev/null || true)

  echo "--------------------------------------------------"
  sleep 1
done

echo "Batch autopilot finished."
