#!/usr/bin/env sh
set -eu

# CI guard: fail on any sorry/admit in Lean sources; report axiom count.
# Exits nonzero if any sorry/admit tokens are found.

# Resolve repo root
SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT_DIR="$(CDPATH= cd -- "$SCRIPT_DIR"/.. && pwd)"
cd "$ROOT_DIR"

# Gather Lean files tracked by git
LEANS="$(git ls-files '*.lean' || true)"

echo "[ci_guard] Scanning for sorry/admit in Lean files..."

# Use ripgrep if available, else fallback to grep
if command -v rg >/dev/null 2>&1; then
  SORRY_MATCHES="$(rg -n --no-messages "\\bsorry\\b" $LEANS || true)"
  ADMIT_MATCHES_RAW="$(rg -n --no-messages "\\badmit\\b" $LEANS || true)"
else
  SORRY_MATCHES="$(grep -n "\\bsorry\\b" $LEANS 2>/dev/null || true)"
  ADMIT_MATCHES_RAW="$(grep -n "\\badmit\\b" $LEANS 2>/dev/null || true)"
fi

# Filter out comments containing the word "admit-free"
if [ -n "$ADMIT_MATCHES_RAW" ]; then
  if command -v rg >/dev/null 2>&1; then
    ADMIT_MATCHES="$(printf "%s\n" "$ADMIT_MATCHES_RAW" | rg -v "admit-free" || true)"
  else
    ADMIT_MATCHES="$(printf "%s\n" "$ADMIT_MATCHES_RAW" | grep -v "admit-free" || true)"
  fi
else
  ADMIT_MATCHES=""
fi

HAS_ISSUES=0

if [ -n "$SORRY_MATCHES" ]; then
  echo "[ci_guard][FAIL] Found 'sorry' occurrences:" >&2
  printf "%s\n" "$SORRY_MATCHES" >&2
  HAS_ISSUES=1
fi

if [ -n "$ADMIT_MATCHES" ]; then
  echo "[ci_guard][FAIL] Found 'admit' occurrences:" >&2
  printf "%s\n" "$ADMIT_MATCHES" >&2
  HAS_ISSUES=1
fi

echo "[ci_guard] Counting axioms..."
if command -v rg >/dev/null 2>&1; then
  AXIOM_COUNT="$(rg -n --no-messages "^axiom\\b" $LEANS | wc -l | tr -d ' ')"
else
  AXIOM_COUNT="$(grep -n "^axiom\\b" $LEANS 2>/dev/null | wc -l | tr -d ' ')"
fi

echo "[ci_guard] axiom count: $AXIOM_COUNT"

if [ "$HAS_ISSUES" -ne 0 ]; then
  echo "[ci_guard] Failing due to sorry/admit occurrences." >&2
  exit 1
fi

echo "[ci_guard] OK: no sorry/admit tokens found."
exit 0


