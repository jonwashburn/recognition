#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

umbrella_defs=$(git grep -P -n "\b(def|lemma|theorem|structure|inductive|class)\b" -- IndisputableMonolith.lean | wc -l | tr -d ' ')
submods_defs=$(git grep -P -n "\b(def|lemma|theorem|structure|inductive|class)\b" -- 'IndisputableMonolith/**' ':!IndisputableMonolith.lean' | wc -l | tr -d ' ')
umbrella_lines=$(wc -l < IndisputableMonolith.lean | tr -d ' ')
submods_lines=$(find IndisputableMonolith -type f -name '*.lean' -print0 | xargs -0 cat | wc -l | tr -d ' ')

total_defs=$((umbrella_defs + submods_defs))
defs_pct=0
if [[ $total_defs -gt 0 ]]; then
  defs_pct=$(( 100 * submods_defs / total_defs ))
fi
total_lines=$((umbrella_lines + submods_lines))
lines_pct=0
if [[ $total_lines -gt 0 ]]; then
  lines_pct=$(( 100 * submods_lines / total_lines ))
fi

printf "defs: %d/%d (%d%%)\n" "$submods_defs" "$total_defs" "$defs_pct"
printf "lines: %d/%d (%d%%)\n" "$submods_lines" "$total_lines" "$lines_pct"


