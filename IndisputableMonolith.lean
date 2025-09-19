import Mathlib
import IndisputableMonolith.Core

/-!
README (Executable Manifest) — Proven Architecture of Reality

To verify in seconds (no knobs), run:
  #eval IndisputableMonolith.URCAdapters.routeA_end_to_end_demo
  #eval IndisputableMonolith.URCAdapters.routeB_closure_report
  #eval IndisputableMonolith.URCAdapters.lambda_report
  #eval IndisputableMonolith.URCAdapters.grand_manifest

These confirm: A (axioms→bridge) ⇒ C; B (generators→bridge) ⇒ C; λ_rec uniqueness holds.
-/

open Classical Function
open Real Complex
open scoped BigOperators

-- (Moved to IndisputableMonolith/Recognition/Certification.lean)end IndisputableMonolith

-- (Moved to IndisputableMonolith/Recognition/Certification.lean)end IndisputableMonolith

-- (Moved to IndisputableMonolith/Recognition/Certification.lean)end IndisputableMonolith
/-- Algebraic identity: `vrot^2 = G Menc / r` for `r > 0`. -/
lemma vrot_sq (S : RotSys) {r : ℝ} (hr : 0 < r) :
  (vrot S r) ^ 2 = S.G * S.Menc r / r := by
  have hnum_nonneg : 0 ≤ S.G * S.Menc r := by
    have hM : 0 ≤ S.Menc r := S.nonnegM r
    exact mul_nonneg (le_of_lt S.posG) hM
  have hfrac_nonneg : 0 ≤ S.G * S.Menc r / r := by
    exact div_nonneg hnum_nonneg (le_of_lt hr)
  simpa [vrot, pow_two] using (Real.mul_self_sqrt hfrac_nonneg)

/-- If the enclosed mass grows linearly, `Menc(r) = α r` with `α ≥ 0`, then the rotation curve is flat:
    `vrot(r) = √(G α)` for all `r > 0`. -/
lemma vrot_flat_of_linear_Menc (S : RotSys) (α : ℝ)
  (hα : 0 ≤ α) (hlin : ∀ {r : ℝ}, 0 < r → S.Menc r = α * r) :
  ∀ {r : ℝ}, 0 < r → vrot S r = Real.sqrt (S.G * α) := by
  intro r hr
  have hM : S.Menc r = α * r := hlin hr
  have hrne : r ≠ 0 := ne_of_gt hr
  have hfrac : S.G * S.Menc r / r = S.G * α := by
    simp [hM, hrne, mul_comm, mul_left_comm, mul_assoc]
  simp [vrot, hfrac]

/-- Under linear mass growth `Menc(r) = α r`, the centripetal acceleration scales as `g(r) = (G α)/r`. -/
lemma g_of_linear_Menc (S : RotSys) (α : ℝ)
  (hlin : ∀ {r : ℝ}, 0 < r → S.Menc r = α * r) :
  ∀ {r : ℝ}, 0 < r → g S r = (S.G * α) / r := by
  intro r hr
  have hM : S.Menc r = α * r := hlin hr
  have hrne : r ≠ 0 := ne_of_gt hr
  simp [g, hM, hrne, mul_comm, mul_left_comm, mul_assoc]

/-- Newtonian rotation curve is flat when the enclosed mass grows linearly:
    if `Menc(r) = γ r` (γ ≥ 0) then `vrot(r) = √(G γ)` for all r > 0. -/
lemma vrot_flat_of_linear_Menc_Newtonian (S : RotSys) (γ : ℝ)
  (hγ : 0 ≤ γ) (hlin : ∀ {r : ℝ}, 0 < r → S.Menc r = γ * r) :
  ∀ {r : ℝ}, 0 < r → vrot S r = Real.sqrt (S.G * γ) := by
  intro r hr
  have hrne : r ≠ 0 := ne_of_gt hr
  have hM : S.Menc r = γ * r := hlin hr
  -- vrot = sqrt(G * Menc / r) = sqrt(G * γ)
  have hnonneg : 0 ≤ S.G * γ := mul_nonneg (le_of_lt S.posG) hγ
  have : S.G * S.Menc r / r = S.G * γ := by
    have : S.Menc r / r = γ := by
      simpa [hM, hrne] using (by field_simp [hrne] : (γ * r) / r = γ)
    simpa [this, mul_comm, mul_left_comm, mul_assoc]
  -- sqrt is monotone on nonnegatives; rewrite
  have hsqrt : Real.sqrt (S.G * S.Menc r / r) = Real.sqrt (S.G * γ) := by
    simpa [this]
  simpa [vrot] using hsqrt
end Rotation
end Gravity
end IndisputableMonolith

-- (Removed duplicate later `Constants` block; canonicalized above.)
end IndisputableMonolith

-- (Removed later duplicate `Verification` block; canonicalized above.)

open Constants
open Constants.RSUnits
open IndisputableMonolith.LightCone

/-- Anchor rescaling relation: scale time and length anchors together by s>0, keep c fixed. -/
structure UnitsRescaled (U U' : RSUnits) : Prop where
  s    : ℝ
  hs   : 0 < s
  tau0 : U'.tau0 = s * U.tau0
  ell0 : U'.ell0 = s * U.ell0
  cfix : U'.c = U.c

/-- A numeric display is dimensionless if it is invariant under anchor rescalings. -/
def Dimensionless (f : RSUnits → ℝ) : Prop := ∀ {U U'}, UnitsRescaled U U' → f U = f U'

/-- Observable: a dimensionless display ready for bridge evaluation. -/
structure Observable where
  f       : RSUnits → ℝ
  dimless : Dimensionless f

/-- Bridge evaluation (A ∘ Q): evaluate any observable under anchors; invariant by construction. -/
@[simp] def BridgeEval (O : Observable) (U : RSUnits) : ℝ := O.f U

/-- Anchor-invariance (Q): evaluation does not depend on rescaled anchors. -/
theorem anchor_invariance (O : Observable) {U U'}
  (hUU' : UnitsRescaled U U') : BridgeEval O U = BridgeEval O U' := O.dimless hUU'

/-- K_A = τ_rec/τ0 as an observable; equality to the constant K yields anchor-invariance. -/
def K_A_obs : Observable :=
{ f := fun U => (Constants.RSUnits.tau_rec_display U) / U.tau0
, dimless := by
    intro U U' h
    have hU  : (tau_rec_display U)  / U.tau0  = Constants.K := Constants.RSUnits.tau_rec_display_ratio U
    have hU' : (tau_rec_display U') / U'.tau0 = Constants.K := Constants.RSUnits.tau_rec_display_ratio U'
    simpa [BridgeEval, hU, hU']
}

/-- K_B = λ_kin/ℓ0 as an observable; equality to the constant K yields anchor-invariance. -/
def K_B_obs : Observable :=
{ f := fun U => (Constants.RSUnits.lambda_kin_display U) / U.ell0
, dimless := by
    intro U U' h
    have hU  : (lambda_kin_display U)  / U.ell0  = Constants.K := Constants.RSUnits.lambda_kin_display_ratio U
    have hU' : (lambda_kin_display U') / U'.ell0 = Constants.K := Constants.RSUnits.lambda_kin_display_ratio U'
    simpa [BridgeEval, hU, hU']
}

-- (Moved to IndisputableMonolith/Verification/KGateBridge.lean)

/-- Evidence bundle for calibration uniqueness: collects K‑gate equality and
    anchor‑invariance of both route displays for traceability. -/
structure CalibrationEvidence : Type where
  k_gate : ∀ U, BridgeEval K_A_obs U = BridgeEval K_B_obs U
  KA_invariant : ∀ {U U'} (h : UnitsRescaled U U'), BridgeEval K_A_obs U = BridgeEval K_A_obs U'
  KB_invariant : ∀ {U U'} (h : UnitsRescaled U U'), BridgeEval K_B_obs U = BridgeEval K_B_obs U'

/-- Canonical evidence derived from the global K‑gate and invariance lemmas. -/
@[simp] def calibrationEvidence_any : CalibrationEvidence :=
{ k_gate := k_gate_bridge_theorem
, KA_invariant := by intro U U' h; exact anchor_invariance _ h
, KB_invariant := by intro U U' h; exact anchor_invariance _ h }

-- (Moved to IndisputableMonolith/Verification/Dimensionless.lean)

/-! ### Discrete cone bound export (clean signature) -/

-- (Moved to IndisputableMonolith/ConeExport/Theorem.lean)
/-! ### Machine-readable claims ledger and K-gate -/

-- (Moved to IndisputableMonolith/Verification/Claims.lean)
deriving DecidableEq, Repr

/-- Status of a claim: proven, failed, or unchecked. -/
inductive ClaimStatus
| proven
| failed
| unchecked
deriving DecidableEq, Repr

/-- A claim over a dimensionless observable with optional tolerance. -/
structure Claim where
  id        : String
  stype     : StatementType
  expr      : Observable
  target    : ℝ
  tol       : Option ℝ := none
  status    : ClaimStatus := .unchecked
deriving Repr
/-- Smart constructor that only accepts anchor-invariant expressions. -/
def dimensionless_claim (id : String) (stype : StatementType)
  (expr : Observable) (target : ℝ) (tol : Option ℝ := none) : Claim :=
{ id := id, stype := stype, expr := expr, target := target, tol := tol, status := .unchecked }

/-- Evaluate a claim under anchors; due to invariance, result is anchor-independent. -/
@[simp] def Claim.value (c : Claim) (U : RSUnits) : ℝ := BridgeEval c.expr U

/-- Check an equality claim by proof; returns updated status. -/
def Claim.checkEq (c : Claim) (U : RSUnits) (h : c.value U = c.target) : Claim :=
  { c with status := .proven }

/-- Check an inequality claim by proof; returns updated status. -/
def Claim.checkLe (c : Claim) (U : RSUnits) (h : c.value U ≤ c.target) : Claim :=
  { c with status := .proven }

/-- The single K-gate inputs for diagnostics and pass/fail witness. -/
structure KGateInput where
  u_ell0  : ℝ
  u_lrec  : ℝ
  rho     : ℝ
  k       : ℝ
  KB      : ℝ
deriving Repr

/-- Result of running the K-gate: pass/fail and a witness inequality statement. -/
structure KGateResult where
  pass    : Bool
  witness : String
deriving Repr

/-- K-gate checker: dimensionless bridge gate |K_A − K_B| ≤ k·u_comb. -/
noncomputable def runKGate (U : RSUnits) (inp : KGateInput) : KGateResult :=
  let KA := BridgeEval K_A_obs U
  let KB := inp.KB
  let ucomb := inp.u_ell0 + inp.u_lrec -- placeholder aggregator; details can be refined
  let lhs := Real.abs (KA - KB)
  let rhs := inp.k * ucomb
  let ok  := decide (lhs ≤ rhs)
  { pass := ok
  , witness := s!"|K_A - K_B| = {lhs} ≤ k·u = {rhs} ⇒ {(if ok then "PASS" else "FAIL")}"
  }

/-! ### Measurement fixtures (parameterized, no axioms) -/

-- (Moved to IndisputableMonolith/Bridge/BridgeData.lean)

/-! ### Machine-checkable index (rendered, #eval-friendly) -/

-- (Moved to IndisputableMonolith/Verification/Rendered.lean)

-- (Moved to IndisputableMonolith/Verification/Rendered.lean)

-- (Moved to IndisputableMonolith/Verification/Rendered.lean)

-- (Moved to IndisputableMonolith/Verification/Rendered.lean)

-- (Moved to IndisputableMonolith/Verification.lean)

/-- Anchor-invariance holds for all registered dimensionless observables. -/
-- (Moved to IndisputableMonolith/Verification.lean)

/-! ### Machine-readable manifest (moved to IndisputableMonolith/Verification/Manifest.lean) -/

/-- ### Ethics invariants (thin Prop layer; refine with concrete lemmas later) -/
-- (Moved to IndisputableMonolith/Ethics/Invariants.lean)

/-! ### URC Adapters (Monolith → URC obligations) -/
-- (Moved to IndisputableMonolith/Recognition/Certification.lean)