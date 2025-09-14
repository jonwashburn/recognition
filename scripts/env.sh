#!/usr/bin/env bash
set -euo pipefail

# Load elan toolchain env if available
if [ -f "$HOME/.elan/env" ]; then
  # shellcheck disable=SC1090
  source "$HOME/.elan/env"
fi

# On macOS, ensure SDKROOT is set so clang can find Apple SDK headers
if [ "${OSTYPE:-}" = "darwin" ] || [[ "${OSTYPE:-}" == darwin* ]]; then
  if command -v xcrun >/dev/null 2>&1; then
    export SDKROOT="$(xcrun --show-sdk-path)"
  fi
  # Optionally, prefer system clang; uncomment to force
  # export LEAN_CC="/usr/bin/clang"
fi

export LC_ALL=C
export LANG=C


