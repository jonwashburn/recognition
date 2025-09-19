#!/usr/bin/env bash
set -euo pipefail

# Usage:
#   ./scripts/autopilot_core.sh [iterations] [optional_wip_file]
# Examples:
#   ./scripts/autopilot_core.sh                 # default 5 iterations
#   ./scripts/autopilot_core.sh 10              # 10 iterations
#   ./scripts/autopilot_core.sh 10 WIP/IndisputableMonolith/RH/RS/Spec.lean

ITER="${1:-5}"
WIP_FILE="${2:-}"

for i in $(seq 1 "$ITER"); do
  echo "=== [autopilot core] iteration $i / $ITER: $(date -u +"%Y-%m-%dT%H:%M:%SZ") ==="

  if [ -x ./scripts/progress.sh ]; then
    ./scripts/progress.sh || true
  fi

  if [ -n "$WIP_FILE" ]; then
    echo "-- building WIP file: $WIP_FILE"
    lake env lean --root=. --o=/dev/null --i=/dev/null --json "$WIP_FILE" | cat || true
  fi

  echo "-- building core umbrella"
  lake build IndisputableMonolith.Core | cat || true

  sleep 2
done


