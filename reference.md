## Certificate Catalog and Hooks

Use this file to look up certificate names, what they assert, and where to hook them into the Lean codebase. Each entry lists:
- Name: Short handle for the certificate
- Claim: Plain-language statement of what is asserted/proved
- Hooks: Existing lemmas/identities/modules to use
- Demo: Suggested `#eval` report name

---

### KGateCert
- Claim: K_A equals K_B across anchors (route display agreement).
- Hooks: `Verification.K_gate_bridge`, `Verification.anchor_invariance`
- Demo: `k_gate_report`

### KIdentitiesCert
- Claim: τ_rec/τ0 = K and λ_kin/ℓ0 = K (dimensionless identities).
- Hooks: `Constants.RSUnits.tau_rec_display_ratio`, `Constants.RSUnits.lambda_kin_display_ratio`
- Demo: `k_identities_report`

### UnitsInvarianceCert
- Claim: Selected observables are invariant under anchor rescalings (dimensionless).
- Hooks: `Verification.UnitsRescaled`, `Verification.anchor_invariance`
- Demo: `units_invariance_report`

### LambdaRecIdentityCert
- Claim: c^3 λ_rec^2/(ħG) = 1/π.
- Hooks: `Source.txt @REALITY_BRIDGE lambda_rec_id`, constants plumbing in `Constants/*`
- Demo: `lambda_rec_identity_report`

### SingleInequalityCert
- Claim: |λ_kin−λ_rec|/λ_rec ≤ k·u_comb with correlation ρ.
- Hooks: `Verification.Observables.uComb`, `Source.txt @AUDIT SINGLE_INEQUALITY`
- Demo: `single_inequality_report`

### ConeBoundCert
- Claim: Discrete light-cone bound holds (causal speed limit).
- Hooks: `LightCone.StepBounds.cone_bound`
- Demo: `cone_bound_report`

### EightTickMinimalCert
- Claim: Minimal period is 8 in D=3.
- Hooks: T6 (`EightTick.minimal_and_exists`), `Source.txt @TIME`
- Demo: `eight_tick_report`

### Window8NeutralityCert
- Claim: 8-window delta sum cancels; block/average identities.
- Hooks: `Source.txt @PATTERN_MEASUREMENT` (PM identities)
- Demo: `window8_report`

### ExactnessCert
- Claim: Closed-chain flux zero implies potential (w = ∇φ) (discrete exactness).
- Hooks: T3/T4 (`Continuity`, `Potential.unique_on_component`)
- Demo: `exactness_report`

### LedgerUnitsCert
- Claim: δ-subgroup ≃ ℤ (δ≠0); uniqueness of representation.
- Hooks: T8 (`LedgerUnits.*`)
- Demo: `ledger_units_report`

### UniqueUpToUnitsCert
- Claim: Bridge uniqueness up to units equivalence.
- Hooks: `RH.RS.Spec.UniqueUpToUnits`
- Demo: `unique_up_to_units_report`
- Status: wired

### Rung45WitnessCert
- Claim: Rung 45 exists; no multiples for n≥2.
- Hooks: `RH.RS.Spec.FortyFiveGapHolds`
- Demo: `rung45_report`

### GapConsequencesCert
- Claim: Packs rung-45, Δ=3/64 time-lag, and sync consequences.
- Hooks: `RH.RS.Spec.fortyfive_gap_consequences_any`
- Demo: `gap_consequences_report`

### FamilyRatioCert
- Claim: Mass ratios are φ^(Δr) at μ*.
- Hooks: `Recognition.mass_ratio_phiPow`
- Demo: `family_ratio_report`

### EqualZAnchorCert
- Claim: Equal‑Z degeneracy at μ* bands; closed-form gap landing.
- Hooks: `Source.txt @SM_MASSES`
- Demo: `equalZ_report`

### RGResidueCert
- Claim: Sector residue models (QED2L/EW; QCD4L+QED2L) used; no self-thresholding for heavies.
- Hooks: `Source.txt @RG_METHODS`
- Demo: `rg_residue_report`

### AblationSensitivityCert
- Claim: Dropping +4, Q^4, or mis-integerization breaks fits per documented deltas.
- Hooks: `Source.txt @RG_METHODS ablations_numeric`
- Demo: `ablation_sensitivity_report`

### SectorYardstickCert
- Claim: Sector `A_B` yardsticks consistent with displays.
- Hooks: `Source.txt @SECTOR_YARDSTICKS`
- Demo: `sector_yardstick_report`
- Status: wired

### TimeKernelDimlessCert
- Claim: ILG time-kernel is dimensionless; `w_time_ratio(τ0,τ0)=1`.
- Hooks: `TruthCore.time_kernel_dimensionless`, `w_time_ratio_ref`
- Demo: `ilg_time_report`
- Status: wired

### EffectiveWeightNonnegCert
- Claim: Effective weight nonnegative and monotone under premises.
- Hooks: `Gravity.effectiveSource_of_nonneg`, `effectiveWeight_monotone`
- Demo: `ilg_effective_report`
- Status: wired

### RotationIdentityCert
- Claim: v^2 = G M_enc/r and flat-curve condition when M_enc ∝ r.
- Hooks: `Gravity.vrot_sq`, `vrot_flat_of_linear_Menc`
- Demo: `rotation_identity_report`
- Status: wired

### ControlsInflateCert
- Claim: Negative controls inflate medians; EFE sensitivity bounded; fairness maintained.
- Hooks: `Source.txt @EXPERIMENTS` (controls, EFE), ILG benchmark scripts
- Demo: `controls_inflate_report`
- Status: wired

### DEC_d∘d_ZeroCert
- Claim: d∘d = 0 (cochain exactness).
- Hooks: `TruthCore.dec_dd_eq_zero`
- Demo: `dec_dd_zero_report`
- Status: wired

### DEC_BianchiCert
- Claim: dF = 0 (Bianchi identity).
- Hooks: `TruthCore.dec_bianchi`
- Demo: `dec_bianchi_report`
- Status: wired

### MaxwellContinuityCert
- Claim: dJ = 0 (current conservation in DEC Maxwell model).
- Hooks: `DEC.CochainSpace.MaxwellModel.current_conservation`
- Demo: `maxwell_continuity_report`
- Status: wired

### BornRuleCert
- Claim: Path measure exp(−C[γ]) implies |ψ|^2.
- Hooks: `Source.txt @QUANTUM BORN_RULE`
- Demo: `born_rule_report`
- Status: wired

### BoseFermiCert
- Claim: Permutation invariance yields Bose/Fermi symmetrization.
- Hooks: `Source.txt @QUANTUM BOSE_FERMI`
- Demo: `bose_fermi_report`

### LNALInvariantsCert
- Claim: Token parity≤1; 8-window neutrality; legal SU(3) triads; 2^10 cycle with FLIP@512.
- Hooks: `Source.txt @LNAL_SPEC`, PNAL→LNAL invariants
- Demo: `lnal_invariants_report`
- Status: wired

### CompilerStaticChecksCert
- Claim: LNAL compiler artifact passes invariants.
- Hooks: `Source.txt @EXPERIMENTS LNAL_Compiler`
- Demo: `compiler_checks_report`
- Status: wired

### OverlapContractionCert
- Claim: Uniform overlap β ⇒ TV contraction α=1−β (finite 3×3 example).
- Hooks: `TruthCore/YM` overlap lemmas
- Demo: `overlap_contraction_report`

### FoldingComplexityCert
- Claim: Folding T_c=O(n^{1/3} log n); readout O(n).
- Hooks: `Source.txt @BIOPHASE` complexity
- Demo: `folding_complexity_report`
- Status: wired

### PDGFitsCert
- Claim: PDG dataset fits with uncertainties/systematics are wired (interface-level placeholder).
- Hooks: `Source.txt @DATASETS PDG_tables`, `SM_masses_repo`; future: CLI pipelines
- Demo: `pdg_fits_report`
- Status: wired

### AbsoluteLayerCert
- Claim: Absolute layer accepts a bridge: UniqueCalibration ∧ MeetsBands.
- Hooks: `RH.RS.UniqueCalibration`, `RH.RS.MeetsBands`
- Demo: `absolute_layer_report`
- Status: wired

### InevitabilityDimlessCert
- Claim: Dimensionless inevitability: ∀ L B, ∃ U, Matches φ L B U.
- Hooks: `RH.RS.Inevitability_dimless`, `RH.RS.Witness.inevitability_dimless_partial`
- Demo: `inevitability_dimless_report`
- Status: wired


