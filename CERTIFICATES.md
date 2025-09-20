# Certificates Manifest

This index lists the wired certificates and their #eval reports. Copy/paste any line into a Lean buffer (with this repo opened) to force elaboration and see a concise OK line.

- Route A wiring
  - `#eval IndisputableMonolith.URCAdapters.routeA_report`
- K identities and gate
  - `#eval IndisputableMonolith.URCAdapters.k_identities_report`
  - `#eval IndisputableMonolith.URCAdapters.k_gate_report`
- Planck identity, single-inequality
  - `#eval IndisputableMonolith.URCAdapters.lambda_rec_identity_report`
  - `#eval IndisputableMonolith.URCAdapters.single_inequality_report`
- Exactness, cone bound, window-8, eight-tick
  - `#eval IndisputableMonolith.URCAdapters.exactness_report`
  - `#eval IndisputableMonolith.URCAdapters.cone_bound_report`
  - `#eval IndisputableMonolith.URCAdapters.window8_report`
  - `#eval IndisputableMonolith.URCAdapters.eight_tick_report`
- Ledger units, rung 45, consequences
  - `#eval IndisputableMonolith.URCAdapters.ledger_units_report`
  - `#eval IndisputableMonolith.URCAdapters.rung45_report`
  - `#eval IndisputableMonolith.URCAdapters.gap_consequences_report`
- Mass ladders
  - `#eval IndisputableMonolith.URCAdapters.family_ratio_report`
  - `#eval IndisputableMonolith.URCAdapters.equalZ_report`
  - `#eval IndisputableMonolith.URCAdapters.pdg_fits_report`
- Quantum
  - `#eval IndisputableMonolith.URCAdapters.born_rule_report`
  - `#eval IndisputableMonolith.URCAdapters.bose_fermi_report`
- Gravity / ILG
  - `#eval IndisputableMonolith.URCAdapters.rotation_identity_report`
  - `#eval IndisputableMonolith.URCAdapters.ilg_time_report`
  - `#eval IndisputableMonolith.URCAdapters.ilg_effective_report`
  - `#eval IndisputableMonolith.URCAdapters.overlap_contraction_report`
- DEC / Maxwell
  - `#eval IndisputableMonolith.URCAdapters.dec_dd_zero_report`
  - `#eval IndisputableMonolith.URCAdapters.dec_bianchi_report`
  - `#eval IndisputableMonolith.URCAdapters.maxwell_continuity_report`
- Absolute layer / Inevitability
  - `#eval IndisputableMonolith.URCAdapters.absolute_layer_report`
  - `#eval IndisputableMonolith.URCAdapters.inevitability_dimless_report`
- LNAL / Compiler / Folding
  - `#eval IndisputableMonolith.URCAdapters.lnal_invariants_report`
  - `#eval IndisputableMonolith.URCAdapters.compiler_checks_report`
  - `#eval IndisputableMonolith.URCAdapters.folding_complexity_report`
- Controls / RG residue
  - `#eval IndisputableMonolith.URCAdapters.controls_inflate_report`
  - `#eval IndisputableMonolith.URCAdapters.rg_residue_report`

Bulk manifest (prints one line per cert):

```lean
#eval IndisputableMonolith.URCAdapters.certificates_manifest
```

Notes:
- All reports are constant-time elaborations (no external IO); safe for CI.
- See `reference.md` for hooks and brief claims; this file is for quick demos.
