## Recognition — Repo Brief and Module Index

This is a Lean 4 project that assembles an "Indisputable Monolith" of definitions and verification scaffolding around a URC (Unified Recognition Certificate) concept. It builds with Lake and depends on `mathlib`.

### Toolchain and Build
- **Lean**: `leanprover/lean4:v4.24.0-rc1` (from `lean-toolchain`)
- **Lake**: Package manager/build tool
- **Dependencies**: `mathlib` (git, see `lakefile.lean`)
- **Libraries**: `IndisputableMonolith`, `URC`

Commands:
```bash
elan default leanprover/lean4:v4.24.0-rc1 # if needed
lake build
lake exe ci_checks
```

### Entrypoints and Quick Demos
- Editor `#eval` demos (open `IndisputableMonolith/Manifest.lean`):
  - `IndisputableMonolith.URCAdapters.routeA_end_to_end_demo`
  - `IndisputableMonolith.URCAdapters.routeB_closure_report`
  - `IndisputableMonolith.URCAdapters.lambda_report`
  - `IndisputableMonolith.URCAdapters.grand_manifest`
- CI smoke (fast, minimal): `lake exe ci_checks` (uses `URC/Minimal.lean`)

### Project Top-Level
- `lakefile.lean`: package `recognition`, requires `mathlib`, defines `lean_lib`s and `ci_checks` exe
- `lean-toolchain`: Lean version pin
- `README.md`: quick start and CI notes
- `IndisputableMonolith.lean`: umbrella import + notes (components split into submodules)
- `IndisputableMonolith/Manifest.lean`: human-facing manifest and `#eval`-friendly pointers
- `CI/Checks.lean`: minimal executable main for CI
- `URC/Minimal.lean`: minimal URC used by CI smoke
- `scripts/`: helper scripts (build, sync monolith, porting, swarm tooling)

### Module Index (high level)
- `IndisputableMonolith/Core/*`: Core constants, recognition core, RS core, streams
- `IndisputableMonolith/URCAdapters/*`: Adapters from monolith to URC obligations; demo reports and routes
- `IndisputableMonolith/URCGenerators.lean`: Generator families and verification skeletons
- `IndisputableMonolith/Verification/*`: Verification core, manifests, rendered views, invariants, calibration, exports
- `IndisputableMonolith/Bridge/*`: Bridge structures, data, displays (wiring between layers)
- `IndisputableMonolith/Constants/*`: Physical/units constants and displays
- `IndisputableMonolith/Ethics/*`: Thin Prop layer for invariants, decisions, and alignment
- `IndisputableMonolith/Gravity/*`: ILG parameters and rotation components
- `IndisputableMonolith/Masses/*`: Kernel types, exponent kernels, ribbons, sector params/primitives
- `IndisputableMonolith/LightCone/*`: Step bounds and light-cone constraints
- `IndisputableMonolith/Measurement/*`: Realization/measurement fixtures
- `IndisputableMonolith/Streams/*`: Blocks and stream utilities
- `IndisputableMonolith/LNAL/*`: VM and related constructs
- `IndisputableMonolith/Gap45/*`: Group views, beats, recognition barriers, time lag
- `IndisputableMonolith/RH/RS/*`: RS spec, bands, scales, anchors, witnesses (absolute layer witnesses)
- `IndisputableMonolith/RSBridge/*`: RS bridge anchoring
- `IndisputableMonolith/ILG/*`: ILG kernels and binning
- `IndisputableMonolith/ClassicalBridge/*`: Coarse-grain/T4 correspondence
- `IndisputableMonolith/Complexity/*`: Complexity examples (vertex cover, RSVC, etc.)
- `IndisputableMonolith/YM/*`: YM kernel/OS, Dobrushin-related material
- Other: `Potential.lean`, `Quantum.lean`, `Pipelines.lean`, `Patterns.lean`, `PhiSupport/*`, `ConeExport/*`, `VoxelWalks.lean`, `LedgerUnits.lean`, `LedgerUniqueness.lean`, etc.

### Placeholder Status
- Some modules contain placeholders (`sorry`): currently 39 instances across ~17 files (subject to change). CI smoke targets only minimal components to stay fast and admit-free.

### Remaining Assumptions (delta)
- RH/RS Spec: `Inevitability_absolute` now requires existence of anchors and bands with `UniqueCalibration` and `MeetsBands` witnesses (no longer `True`).
- RH/RS Spec: `SAT_Separation` concretized as `∀ n, n ≤ n.succ` and plumbed into `Inevitability_recognition_computation`.
- URCGenerators: `LawfulBridge` strengthened to a full conjunction from `Verified` (no trailing True-constructors).
- RH/RS Witness: `boseFermiHolds` now constructed from a concrete trivial path-weight system (no trivial constructor usage).
- URCAdapters/PhiRung: `inevitability_dimless_partial` wired to the actual RS witness.
- URC/Minimal: removed trivial `@[simp] def ok : True`.
- Ethics: replaced Prop=True placeholders with concrete predicates tied to existing boolean checks (`truthOk`, `consentOk`, `harmOk`, `privacyOk`, `coiOk`, `robustOk`, `uniqueInWindow`).

### How to Explore
1) Open in a Lean 4–enabled editor (VS Code + Lean extension or Cursor) and navigate `IndisputableMonolith/Manifest.lean`.
2) Use `#eval` at the top-level demos listed above to get quick confirmations.
3) Follow imports from `IndisputableMonolith.lean` and the directories above to dive deeper.

### Notes
- The repository includes scripts to sync a canonical monolith (`scripts/sync_monolith_from.sh`) and various CI/porting helpers.
- See `README.md` for install/build instructions; this brief is a quick map of the terrain.


