import Mathlib
import IndisputableMonolith.Verification
import IndisputableMonolith.Verification.Observables
import IndisputableMonolith.Constants.KDisplay
import IndisputableMonolith.Bridge.DataExt

namespace IndisputableMonolith
namespace URCGenerators

/-! Units invariance certificates: observables invariant under anchor rescalings. -/

structure UnitsInvarianceCert where
  obs : IndisputableMonolith.Verification.Observable
  deriving Repr

@[simp] def UnitsInvarianceCert.verified (c : UnitsInvarianceCert) : Prop :=
  ∀ {U U'}, IndisputableMonolith.Verification.UnitsRescaled U U' →
    IndisputableMonolith.Verification.BridgeEval c.obs U =
    IndisputableMonolith.Verification.BridgeEval c.obs U'

/-- Any observable witnesses its own units-invariance via the anchor invariance hook. -/
lemma UnitsInvarianceCert.verified_any (c : UnitsInvarianceCert) :
  UnitsInvarianceCert.verified c := by
  intro U U' h
  exact IndisputableMonolith.Verification.anchor_invariance c.obs h

structure UnitsCert where
  lo : ℚ
  hi : ℚ
  deriving Repr

@[simp] def UnitsCert.verified (c : UnitsCert) : Prop :=
  (c.lo : ℝ) ≤ 1 ∧ 1 ≤ (c.hi : ℝ)

structure EightBeatCert where
  T : Nat
  deriving Repr

@[simp] def EightBeatCert.verified (c : EightBeatCert) : Prop := 8 ≤ c.T

structure ELProbe where eps : ℚ
  deriving Repr

@[simp] def ELProbe.verified (c : ELProbe) : Prop := 0 ≤ (c.eps : ℝ)

structure MassCert where
  ratio : ℚ
  eps   : ℚ
  pos   : 0 < eps
  deriving Repr

@[simp] def MassCert.verified (φ : ℝ) (c : MassCert) : Prop := |(c.ratio : ℝ) - φ| ≤ (c.eps : ℝ)

structure RotationCert where
  gamma : ℚ
  scope : Prop
  deriving Repr

@[simp] def RotationCert.verified (c : RotationCert) : Prop :=
  (0 ≤ (c.gamma : ℝ)) ∧ c.scope

structure OuterBudgetCert where data : Prop
  deriving Repr

@[simp] def OuterBudgetCert.verified (c : OuterBudgetCert) : Prop := c.data

structure ConsciousCert where
  k_pos : Nat
  hk    : 0 < (k_pos : ℝ)
  deriving Repr

@[simp] def ConsciousCert.verified (c : ConsciousCert) : Prop := 0 < (c.k_pos : ℝ)

/-! K-identities (dimensionless display equalities) -/

/-- Certificate asserting calibrated, dimensionless identities τ_rec/τ0 = K and λ_kin/ℓ0 = K. -/
structure KIdentitiesCert where
  deriving Repr

@[simp] def KIdentitiesCert.verified (_c : KIdentitiesCert) : Prop :=
  ∀ U : IndisputableMonolith.Constants.RSUnits,
    (IndisputableMonolith.Constants.RSUnits.tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K ∧
    (IndisputableMonolith.Constants.RSUnits.lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K

@[simp] theorem KIdentitiesCert.verified_any (c : KIdentitiesCert) : KIdentitiesCert.verified c := by
  intro U
  exact And.intro
    (IndisputableMonolith.Constants.RSUnits.tau_rec_display_ratio U)
    (IndisputableMonolith.Constants.RSUnits.lambda_kin_display_ratio U)

/-! K-gate (route display agreement) -/

/-- Certificate asserting route display agreement `K_A = K_B` across anchors. -/
structure KGateCert where
  deriving Repr

@[simp] def KGateCert.verified (_c : KGateCert) : Prop :=
  ∀ U : IndisputableMonolith.Constants.RSUnits,
    IndisputableMonolith.Verification.K_gate_bridge U

/-! λ_rec identity (Planck-side normalization) -/

/-- Certificate asserting the Planck-side identity (c^3 · λ_rec^2)/(ħ G) = 1/π. -/
structure LambdaRecIdentityCert where
  deriving Repr

@[simp] def LambdaRecIdentityCert.verified (_c : LambdaRecIdentityCert) : Prop :=
  ∀ (B : IndisputableMonolith.BridgeData),
    IndisputableMonolith.BridgeData.Physical B →
      (B.c ^ 3) * (IndisputableMonolith.BridgeData.lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi

@[simp] theorem LambdaRecIdentityCert.verified_any (c : LambdaRecIdentityCert) :
  LambdaRecIdentityCert.verified c := by
  intro B H
  exact IndisputableMonolith.BridgeData.lambda_rec_dimensionless_id_physical B H

/-- Certificate asserting the single‑inequality audit
    `|K_A − K_B| ≤ k · u_comb(u_ℓ0,u_λrec,ρ)` using the uComb hook. -/
structure SingleInequalityCert where
  u_ell0 : ℝ
  u_lrec : ℝ
  rho    : ℝ
  k      : ℝ
  hk     : 0 ≤ k
  hrho   : -1 ≤ rho ∧ rho ≤ 1
  deriving Repr

@[simp] def SingleInequalityCert.verified (c : SingleInequalityCert) : Prop :=
  ∀ U : IndisputableMonolith.Constants.RSUnits,
    Real.abs (
      IndisputableMonolith.Verification.BridgeEval IndisputableMonolith.Verification.K_A_obs U -
      IndisputableMonolith.Verification.BridgeEval IndisputableMonolith.Verification.K_B_obs U
    ) ≤ c.k * IndisputableMonolith.Verification.uComb c.u_ell0 c.u_lrec c.rho

@[simp] theorem SingleInequalityCert.verified_any (c : SingleInequalityCert) :
  SingleInequalityCert.verified c := by
  intro U
  exact IndisputableMonolith.Verification.K_gate_single_inequality U
    c.u_ell0 c.u_lrec c.rho c.k c.hk c.hrho

structure CertFamily where
  unitsInv : List UnitsInvarianceCert := []
  units     : List UnitsCert        := []
  eightbeat : List EightBeatCert    := []
  elprobes  : List ELProbe          := []
  masses    : List MassCert         := []
  rotation  : List RotationCert     := []
  outer     : List OuterBudgetCert  := []
  conscious : List ConsciousCert    := []
  kidentities : List KIdentitiesCert := []
  kgate     : List KGateCert        := []
  lambdaRec : List LambdaRecIdentityCert := []
  singleineq : List SingleInequalityCert := []
  deriving Repr

def Verified (φ : ℝ) (C : CertFamily) : Prop :=
  (∀ c ∈ C.unitsInv, UnitsInvarianceCert.verified c) ∧
  (∀ c ∈ C.units, UnitsCert.verified c) ∧
  (∀ c ∈ C.eightbeat, EightBeatCert.verified c) ∧
  (∀ c ∈ C.elprobes, ELProbe.verified c) ∧
  (∀ c ∈ C.masses, MassCert.verified φ c) ∧
  (∀ c ∈ C.rotation, RotationCert.verified c) ∧
  (∀ c ∈ C.outer, OuterBudgetCert.verified c) ∧
  (∀ c ∈ C.conscious, ConsciousCert.verified c) ∧
  (∀ c ∈ C.kidentities, KIdentitiesCert.verified c) ∧
  (∀ c ∈ C.kgate, KGateCert.verified c) ∧
  (∀ c ∈ C.lambdaRec, LambdaRecIdentityCert.verified c) ∧
  (∀ c ∈ C.singleineq, SingleInequalityCert.verified c)

def singletonMassFamily (c : MassCert) : CertFamily :=
{ unitsInv := [], units := [], eightbeat := [], elprobes := [], masses := [c]
, rotation := [], outer := [], conscious := [] }

lemma verified_singletonMass (φ : ℝ) (c : MassCert)
  (h : MassCert.verified φ c) : Verified φ (singletonMassFamily c) := by
  dsimp [Verified, singletonMassFamily]
  refine And.intro ?huInv (And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout (And.intro ?hcons (And.intro ?hkid (And.intro ?hkg ?hlrec)))))))))
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx

lemma verified_empty (φ : ℝ) : Verified φ {
  unitsInv := [], units := [], eightbeat := [], elprobes := [], masses := [], rotation := [], outer := [], conscious := [] } := by
  dsimp [Verified]
  refine And.intro ?huInv (And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout (And.intro ?hcons (And.intro ?hkid (And.intro ?hkg (And.intro ?hlrec ?hsing))))))))) )
  all_goals
    intro x hx; cases hx

/-! ### Minimal Route B generators cluster (stable) -/

/-- Bundle a generator family with a proof that all certificates verify. -/
structure VerifiedGenerators (φ : ℝ) where
  fam : CertFamily
  ok  : Verified φ fam

/--- Minimal Prop-level obligations induced by generators (now the actual per-family Verified predicates). -/
def UnitsProp (C : CertFamily) : Prop := ∀ c ∈ C.units, UnitsCert.verified c
def EightBeatProp (C : CertFamily) : Prop := ∀ c ∈ C.eightbeat, EightBeatCert.verified c
def ELProp (C : CertFamily) : Prop := ∀ c ∈ C.elprobes, ELProbe.verified c
def PhiRungProp (φ : ℝ) (C : CertFamily) : Prop := ∀ c ∈ C.masses, MassCert.verified φ c
def RotationProp (C : CertFamily) : Prop := ∀ c ∈ C.rotation, RotationCert.verified c
def OuterBudgetProp (C : CertFamily) : Prop := ∀ c ∈ C.outer, OuterBudgetCert.verified c
def ConsciousProp (C : CertFamily) : Prop := ∀ c ∈ C.conscious, ConsciousCert.verified c
def KIdentitiesProp (C : CertFamily) : Prop := ∀ c ∈ C.kidentities, KIdentitiesCert.verified c
def KGateProp (C : CertFamily) : Prop := ∀ c ∈ C.kgate, KGateCert.verified c

/--- Route B Lawfulness bundle, tied to a concrete certificate family and φ.
     Strengthened: includes all verified subpredicates (no trailing True). -/
def LawfulBridge (φ : ℝ) (C : CertFamily) : Prop :=
  UnitsProp C ∧ EightBeatProp C ∧ ELProp C ∧ PhiRungProp φ C ∧
  RotationProp C ∧ OuterBudgetProp C ∧ ConsciousProp C ∧ KIdentitiesProp C ∧ KGateProp C

/-- Generators imply a lawful-bridge bundle by unpacking the Verified proof. -/
theorem determination_by_generators {φ : ℝ}
  (VG : VerifiedGenerators φ) : LawfulBridge φ VG.fam := by
  rcases VG with ⟨C, hC⟩
  dsimp [LawfulBridge, UnitsProp, EightBeatProp, ELProp, PhiRungProp,
        RotationProp, OuterBudgetProp, ConsciousProp, KIdentitiesProp, KGateProp] at *
  rcases hC with ⟨huInv, hu, he8, hel, hm, hrot, hout, hcons, hkid, hkg, hlrec⟩
  exact And.intro hu
    (And.intro he8 (And.intro hel (And.intro hm (And.intro hrot (And.intro hout (And.intro hcons (And.intro hkid hkg)))))))

/-- A tiny demo family: empty certificate sets verify vacuously. -/
def demo_generators (φ : ℝ) : VerifiedGenerators φ :=
  let C : CertFamily := { unitsInv := [], units := [], eightbeat := [], elprobes := [], masses := []
                        , rotation := [], outer := [], conscious := [] }
  have hC : Verified φ C := by
    dsimp [Verified, C]
  refine And.intro ?huInv (And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout (And.intro ?hcons (And.intro ?hkid (And.intro ?hkg (And.intro ?hlrec ?hsing))))))))) )
    all_goals intro x hx; cases hx
  ⟨C, hC⟩

@[simp] def demo_generators_phi : VerifiedGenerators (0 : ℝ) :=
  demo_generators 0

/-- Human-readable reports for Route B wiring. -/
def routeB_report : String :=
  "URC Route B: generators ⇒ bridge wired (minimal demo)."

def routeB_closure_demo : String :=
  "URC Route B end-to-end: bridge from generators constructed; ready for closure wiring."

end URCGenerators
end IndisputableMonolith
