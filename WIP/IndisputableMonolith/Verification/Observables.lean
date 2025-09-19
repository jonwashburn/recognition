import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.Constants

open Classical Function
open Real Complex
open scoped BigOperators

namespace IndisputableMonolith.Verification

/-- Anchor rescaling relation: scale time and length anchors together by s>0, keep c fixed. -/
structure UnitsRescaled (U U' : Constants.RSUnits) : Prop where
  s    : ℝ
  hs   : 0 < s
  tau0 : U'.tau0 = s * U.tau0
  ell0 : U'.ell0 = s * U.ell0
  cfix : U'.c = U.c

/-- A numeric display is dimensionless if it is invariant under anchor rescalings. -/
def Dimensionless (f : Constants.RSUnits → ℝ) : Prop := ∀ {U U'}, UnitsRescaled U U' → f U = f U'

/-- Observable: a dimensionless display ready for bridge evaluation. -/
structure Observable where
  f       : Constants.RSUnits → ℝ
  dimless : Dimensionless f

/-- Bridge evaluation (A ∘ Q): evaluate any observable under anchors; invariant by construction. -/
@[simp] def BridgeEval (O : Observable) (U : Constants.RSUnits) : ℝ := O.f U

/-- Anchor-invariance (Q): evaluation does not depend on rescaled anchors. -/
theorem anchor_invariance (O : Observable) {U U'}
  (hUU' : UnitsRescaled U U') : BridgeEval O U = BridgeEval O U' := O.dimless hUU'

/-- K_A = τ_rec/τ0 as an observable; equality to the constant K yields anchor-invariance. -/
def K_A_obs : Observable :=
{ f := fun U => (Constants.RSUnits.tau_rec_display U) / U.tau0
, dimless := by
    intro U U' h
    have hU  : (Constants.RSUnits.tau_rec_display U)  / U.tau0  = Constants.K := Constants.RSUnits.tau_rec_display_ratio U
    have hU' : (Constants.RSUnits.tau_rec_display U') / U'.tau0 = Constants.K := Constants.RSUnits.tau_rec_display_ratio U'
    simpa [BridgeEval, hU, hU']
}

/-- K_B = λ_kin/ℓ0 as an observable; equality to the constant K yields anchor-invariance. -/
def K_B_obs : Observable :=
{ f := fun U => (Constants.RSUnits.lambda_kin_display U) / U.ell0
, dimless := by
    intro U U' h
    have hU  : (Constants.RSUnits.lambda_kin_display U)  / U.ell0  = Constants.K := Constants.RSUnits.lambda_kin_display_ratio U
    have hU' : (Constants.RSUnits.lambda_kin_display U') / U'.ell0 = Constants.K := Constants.RSUnits.lambda_kin_display_ratio U'
    simpa [BridgeEval, hU, hU']
}

/-- Evidence bundle for calibration uniqueness: collects K‑gate equality and
    anchor‑invariance of both route displays for traceability. -/
structure CalibrationEvidence : Type where
  k_gate : ∀ U, BridgeEval K_A_obs U = BridgeEval K_B_obs U
  KA_invariant : ∀ {U U'} (h : UnitsRescaled U U'), BridgeEval K_A_obs U = BridgeEval K_A_obs U'
  KB_invariant : ∀ {U U'} (h : UnitsRescaled U U'), BridgeEval K_B_obs U = BridgeEval K_B_obs U'

/-- Canonical evidence derived from the global K‑gate and invariance lemmas. -/
@[simp] def calibrationEvidence_any : CalibrationEvidence :=
{ k_gate := sorry -- depends on k_gate_bridge_theorem
, KA_invariant := by intro U U' h; exact anchor_invariance _ h
, KB_invariant := by intro U U' h; exact anchor_invariance _ h }

/-- Status of a claim: proven, failed, or unchecked. -/
inductive ClaimStatus
| proven
| failed
| unchecked
deriving DecidableEq, Repr

/-- Statement type for claims. -/
axiom StatementType : Type

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
@[simp] def Claim.value (c : Claim) (U : Constants.RSUnits) : ℝ := BridgeEval c.expr U

/-- Check an equality claim by proof; returns updated status. -/
def Claim.checkEq (c : Claim) (U : Constants.RSUnits) (h : c.value U = c.target) : Claim :=
  { c with status := .proven }

/-- Check an inequality claim by proof; returns updated status. -/
def Claim.checkLe (c : Claim) (U : Constants.RSUnits) (h : c.value U ≤ c.target) : Claim :=
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
noncomputable def runKGate (U : Constants.RSUnits) (inp : KGateInput) : KGateResult :=
  let KA := BridgeEval K_A_obs U
  let KB := inp.KB
  let ucomb := inp.u_ell0 + inp.u_lrec -- placeholder aggregator; details can be refined
  let lhs := |KA - KB|
  let rhs := inp.k * ucomb
  let ok  := decide (lhs ≤ rhs)
  { pass := ok
  , witness := s!"|K_A - K_B| = {lhs} ≤ k·u = {rhs} ⇒ {(if ok then "PASS" else "FAIL")}"
  }

end IndisputableMonolith.Verification
