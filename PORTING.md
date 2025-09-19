Multi-agent porting workflow

This repo is being migrated from the umbrella `IndisputableMonolith.lean` to structured submodules while keeping builds green.

Coordination
- `PORTMAP.json` lists small clusters with status: `pending | in_progress | done` and owner.
- Agents claim a cluster before editing to avoid overlap:
  - `scripts/claim.sh <cluster-id> <owner>`
- Prefer separate directories per agent scope to minimize collisions.
- Only a gatekeeper updates `IndisputableMonolith/Core.lean` imports and removes code from the umbrella.

Picking clusters
- Prefer dependency-light blocks (~100–250 lines):
  - `IndisputableMonolith/{Patterns, Streams, URCGenerators, Recognition (light parts)}`
  - `IndisputableMonolith/RH/RS/{Anchors,Bands,Scales}`
  - `IndisputableMonolith/Complexity/{VertexCover,RSVC,BalancedParityHidden}`
- Avoid heavy sections for now: `Verification`, `URCAdapters`, `TruthCore`, `MaxwellDEC`, `Quantum`.

Build checks
- Fast incremental: `lake build IndisputableMonolith -j8`
- If needed: `lake env -- lean -q IndisputableMonolith/Core.lean -o /dev/null` and umbrella.

Progress metrics
- `scripts/progress.sh` prints percentage by defs and lines migrated.

Commit/PR
- Reuse the working branch and PR; one cluster per commit with message:
  - `Port stable cluster: <short description> (green)`

Rules
- Keep top-level umbrella importing only `IndisputableMonolith.Core`.
- Do not introduce ProofWidgets.
- No net deletion > 50 lines per session.
- Skip any cluster that doesn’t close cleanly within minutes.



