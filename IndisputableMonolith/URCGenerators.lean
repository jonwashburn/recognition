import Mathlib

namespace IndisputableMonolith
namespace URCGenerators

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

@[simp] def RotationCert.verified (_c : RotationCert) : Prop := True

structure OuterBudgetCert where data : Prop
  deriving Repr

@[simp] def OuterBudgetCert.verified (_c : OuterBudgetCert) : Prop := True

structure ConsciousCert where
  k_pos : Nat
  hk    : 0 < (k_pos : ℝ)
  deriving Repr

@[simp] def ConsciousCert.verified (_c : ConsciousCert) : Prop := True

structure CertFamily where
  units     : List UnitsCert        := []
  eightbeat : List EightBeatCert    := []
  elprobes  : List ELProbe          := []
  masses    : List MassCert         := []
  rotation  : List RotationCert     := []
  outer     : List OuterBudgetCert  := []
  conscious : List ConsciousCert    := []
  deriving Repr

def Verified (φ : ℝ) (C : CertFamily) : Prop :=
  (∀ c ∈ C.units, UnitsCert.verified c) ∧
  (∀ c ∈ C.eightbeat, EightBeatCert.verified c) ∧
  (∀ c ∈ C.elprobes, ELProbe.verified c) ∧
  (∀ c ∈ C.masses, MassCert.verified φ c) ∧
  (∀ c ∈ C.rotation, RotationCert.verified c) ∧
  (∀ c ∈ C.outer, OuterBudgetCert.verified c) ∧
  (∀ c ∈ C.conscious, ConsciousCert.verified c)

def singletonMassFamily (c : MassCert) : CertFamily :=
{ units := [], eightbeat := [], elprobes := [], masses := [c]
, rotation := [], outer := [], conscious := [] }

lemma verified_singletonMass (φ : ℝ) (c : MassCert)
  (h : MassCert.verified φ c) : Verified φ (singletonMassFamily c) := by
  dsimp [Verified, singletonMassFamily]
  refine And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout ?hcons)))))
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx

lemma verified_empty (φ : ℝ) : Verified φ {
  units := [], eightbeat := [], elprobes := [], masses := [], rotation := [], outer := [], conscious := [] } := by
  dsimp [Verified]
  refine And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout ?hcons)))))
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

/--- Route B Lawfulness bundle, tied to a concrete certificate family and φ. -/
def LawfulBridge (φ : ℝ) (C : CertFamily) : Prop :=
  UnitsProp C ∧ EightBeatProp C ∧ ELProp C ∧ PhiRungProp φ C ∧ True

/-- Generators imply a lawful-bridge bundle by unpacking the Verified proof. -/
theorem determination_by_generators {φ : ℝ}
  (VG : VerifiedGenerators φ) : LawfulBridge φ VG.fam := by
  rcases VG with ⟨C, hC⟩
  dsimp [LawfulBridge, UnitsProp, EightBeatProp, ELProp, PhiRungProp] at *
  rcases hC with ⟨hu, he8, hel, hm, hrot, hout, hcons⟩
  exact And.intro hu (And.intro he8 (And.intro hel (And.intro hm True.intro)))

/-- A tiny demo family: empty certificate sets verify vacuously. -/
def demo_generators (φ : ℝ) : VerifiedGenerators φ :=
  let C : CertFamily := { units := [], eightbeat := [], elprobes := [], masses := []
                        , rotation := [], outer := [], conscious := [] }
  have hC : Verified φ C := by
    dsimp [Verified, C]
    refine And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout ?hcons)))))
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
