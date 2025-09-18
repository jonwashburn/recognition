#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ $# -lt 2 ]]; then
  echo "Usage: $0 <cluster-id> <owner>"
  exit 1
fi
id="$1"
owner="$2"

# naive jq-free edit: create a backup and replace status/owner for matching id
cp PORTMAP.json PORTMAP.json.bak
awk -v id="$id" -v owner="$owner" '
  BEGIN{RS="\n"; FS=":"}
  {
    print $0
  }
' PORTMAP.json > PORTMAP.json.tmp
# minimal sed: switch first matching block to in_progress and set owner
# Note: this is simplistic; for robust edits, install jq.
sed -i '' -e "/\"id\": \"$id\"/,/}/ { s/\"status\": \"pending\"/\"status\": \"in_progress\"/; s/\"owner\": \"\"/\"owner\": \"$owner\"/ }" PORTMAP.json

echo "Claimed cluster $id for $owner"
