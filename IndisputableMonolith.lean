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

section ConeExport

variable {α : Type _}
variable (K : Causality.Kinematics α)
variable (U : Constants.RSUnits)
variable (time rad : α → ℝ)

/-- Verification-level cone bound: if per-step bounds hold, any `n`-step reach obeys
    `rad y - rad x ≤ U.c * (time y - time x)` with no `n` in the statement. -/
theorem cone_bound_export
  (H : LightCone.StepBounds K U time rad)
  {n x y} (h : Causality.ReachN K n x y) :
  rad y - rad x ≤ U.c * (time y - time x) := by
  simpa using (LightCone.StepBounds.cone_bound (K:=K) (U:=U) (time:=time) (rad:=rad) H h)
end ConeExport
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

/-- External bridge anchors provided as data (no axioms): G, ħ, c, plus display anchors. -/
structure BridgeData where
  G     : ℝ
  hbar  : ℝ
  c     : ℝ
  tau0  : ℝ
  ell0  : ℝ
  deriving Repr

namespace BridgeData

@[simp] def K_A (_ : BridgeData) : ℝ := Constants.K

/-- Recognition length from anchors: λ_rec = √(ħ G / c^3). -/
@[simp] def lambda_rec (B : BridgeData) : ℝ :=
  Real.sqrt (B.hbar * B.G / (Real.pi * (B.c ^ 3)))

/-- Minimal physical assumptions on bridge anchors reused by analytical lemmas. -/
structure Physical (B : BridgeData) : Prop where
  c_pos    : 0 < B.c
  hbar_pos : 0 < B.hbar
  G_pos    : 0 < B.G

/-- Dimensionless identity for λ_rec (under mild physical positivity assumptions):
    (c^3 · λ_rec^2) / (ħ G) = 1/π. -/
lemma lambda_rec_dimensionless_id (B : BridgeData)
  (hc : 0 < B.c) (hh : 0 < B.hbar) (hG : 0 < B.G) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hc3_pos : 0 < B.c ^ 3 := by
    have := pow_pos hc (3 : Nat)
    simpa using this
  have hden_pos : 0 < Real.pi * (B.c ^ 3) := mul_pos hpi_pos hc3_pos
  have hnum_nonneg : 0 ≤ B.hbar * B.G := mul_nonneg (le_of_lt hh) (le_of_lt hG)
  have hrad_nonneg : 0 ≤ (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  -- Square of sqrt is the radicand
  have hsq : (lambda_rec B) ^ 2
      = (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) := by
    dsimp [lambda_rec]
    have := Real.mul_self_sqrt hrad_nonneg
    simpa [pow_two] using this
  -- Compute the dimensionless ratio
  have hprod_ne : B.hbar * B.G ≠ 0 := mul_ne_zero (ne_of_gt hh) (ne_of_gt hG)
  have hc3_ne : B.c ^ 3 ≠ 0 := ne_of_gt hc3_pos
  calc
    (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G)
        = (B.c ^ 3) * (((B.hbar * B.G) / (Real.pi * (B.c ^ 3))) / (B.hbar * B.G)) := by simpa [hsq]
    _   = (B.c ^ 3) * ((B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G))) := by
          -- a*b/c = a*(b/c); (x/y)/z = x/(y*z)
          have : ((B.hbar * B.G) / (Real.pi * (B.c ^ 3))) / (B.hbar * B.G)
                    = (B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G)) := by
            simpa [div_div, mul_comm, mul_left_comm, mul_assoc]
          -- reorder factors to isolate 1/(π c^3)
          calc
            (B.c ^ 3) * (((B.hbar * B.G) / (Real.pi * (B.c ^ 3))) / (B.hbar * B.G))
                = (B.c ^ 3) * ((B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G))) := by simpa [this]
            _ = ((B.c ^ 3) / (Real.pi * (B.c ^ 3))) * ((B.hbar * B.G) / (B.hbar * B.G)) := by
                field_simp
    _   = ((B.c ^ 3) / (Real.pi * (B.c ^ 3))) * 1 := by simp [hprod_ne]
    _   = 1 / Real.pi := by
          have : (B.c ^ 3) / (B.c ^ 3) = (1 : ℝ) := by simpa [div_self hc3_ne]
          -- (a)/(π a) = (1/π) * (a/a)
          have := by
            have : (B.c ^ 3) / (Real.pi * (B.c ^ 3)) = (1 / Real.pi) * ((B.c ^ 3) / (B.c ^ 3)) := by
              field_simp
            simpa [this]
          -- simplify to 1/π
          simpa [this]

/-- Dimensionless identity packaged with a physical-assumptions helper. -/
lemma lambda_rec_dimensionless_id_physical (B : BridgeData) (H : Physical B) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi :=
  lambda_rec_dimensionless_id B H.c_pos H.hbar_pos H.G_pos

/-- Positivity of λ_rec under physical assumptions. -/
lemma lambda_rec_pos (B : BridgeData) (H : Physical B) : 0 < lambda_rec B := by
  dsimp [lambda_rec]
  have num_pos : 0 < B.hbar * B.G := mul_pos H.hbar_pos H.G_pos
  have den_pos : 0 < Real.pi * (B.c ^ 3) := by
    have hc3 : 0 < B.c ^ 3 := by simpa using pow_pos H.c_pos (3 : Nat)
    exact mul_pos Real.pi_pos hc3
  have : 0 < (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) := div_pos num_pos den_pos
  exact Real.sqrt_pos.mpr this

@[simp] def K_B (B : BridgeData) : ℝ :=
  lambda_rec B / B.ell0

/-- Combined uncertainty aggregator (placeholder policy). -/
@[simp] def u_comb (_ : BridgeData) (u_ell0 u_lrec : ℝ) : ℝ := u_ell0 + u_lrec

/-- Symbolic K-gate Z-score witness: Z = |K_A − K_B| / (k·u_comb). -/
@[simp] def Zscore (B : BridgeData) (u_ell0 u_lrec k : ℝ) : ℝ :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  (Real.abs (KA - KB)) / (k * u)

/-- Boolean pass at threshold k: Z ≤ 1. Publishes the exact Z expression. -/
@[simp] def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  decide ((Zscore B u_ell0 u_lrec k) ≤ 1)

/-- Full witness record for publication. -/
structure Witness where
  KA : ℝ
  KB : ℝ
  u  : ℝ
  Z  : ℝ
  pass : Bool
deriving Repr

@[simp] def witness (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Witness :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  let Z  := (Real.abs (KA - KB)) / (k * u)
  { KA := KA, KB := KB, u := u, Z := Z, pass := decide (Z ≤ 1) }

/-- Tick from anchors via hop map λ_rec = c · τ0. -/
@[simp] def tau0 (B : BridgeData) : ℝ := lambda_rec B / B.c

/-- Coherence energy: E_coh = φ^-5 · (2π ħ / τ0). -/
@[simp] def E_coh (B : BridgeData) : ℝ :=
  (1 / (Constants.phi ^ (5 : Nat))) * (2 * Real.pi * B.hbar / (tau0 B))

/-- Dimensionless inverse fine-structure constant (seed–gap–curvature). -/
@[simp] def alphaInv : ℝ :=
  4 * Real.pi * 11 - (Real.log Constants.phi + (103 : ℝ) / (102 * Real.pi ^ 5))

/-- Fine-structure constant α. -/
@[simp] def alpha : ℝ := 1 / alphaInv

/-- Electron mass in units of E_coh: m_e/E_coh = Φ(r_e + 𝔽(Z_e)). -/
@[simp] def m_e_over_Ecoh : ℝ :=
  IndisputableMonolith.Recognition.PhiPow
    ((IndisputableMonolith.Recognition.r IndisputableMonolith.Recognition.Species.e : ℝ)
     + IndisputableMonolith.Recognition.Fgap (IndisputableMonolith.Recognition.Z IndisputableMonolith.Recognition.Species.e))

/-- Electron mass: m_e = (m_e/E_coh) · E_coh. -/
@[simp] def m_e (B : BridgeData) : ℝ := m_e_over_Ecoh * E_coh B

/-- Bohr radius a0 = ħ / (m_e c α). -/
@[simp] def a0_bohr (B : BridgeData) : ℝ :=
  B.hbar / (m_e B * B.c * alpha)

end BridgeData

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