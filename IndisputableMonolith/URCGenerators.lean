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

/-- A packaged set of generators that already satisfy verification for a given φ. -/
structure VerifiedGenerators (φ : ℝ) where
  C  : CertFamily
  ok : Verified φ C

/-- Trivial, always-verified generators: the empty certification family. -/
@[simp] def demo_generators (φ : ℝ) : VerifiedGenerators φ :=
  { C := { units := [], eightbeat := [], elprobes := [], masses := []
         , rotation := [], outer := [], conscious := [] }
  , ok := verified_empty φ }

@[simp] def demo_generators_phi : VerifiedGenerators (0 : ℝ) := demo_generators 0

/-- Placeholder witness: generators determine a viable bridge policy (Prop-level stub). -/
@[simp] def determination_by_generators {φ : ℝ}
  (VG : VerifiedGenerators φ) : True := True.intro

/-- Append two certification families by concatenating their lists. -/
def append (C₁ C₂ : CertFamily) : CertFamily :=
{ units     := C₁.units ++ C₂.units
, eightbeat := C₁.eightbeat ++ C₂.eightbeat
, elprobes  := C₁.elprobes ++ C₂.elprobes
, masses    := C₁.masses ++ C₂.masses
, rotation  := C₁.rotation ++ C₂.rotation
, outer     := C₁.outer ++ C₂.outer
, conscious := C₁.conscious ++ C₂.conscious }

/-- Verification is closed under appending certification families. -/
lemma verified_append (φ : ℝ) (C₁ C₂ : CertFamily)
  (h₁ : Verified φ C₁) (h₂ : Verified φ C₂) : Verified φ (append C₁ C₂) := by
  dsimp [Verified, append] at *
  rcases h₁ with ⟨h₁u, h₁e8, h₁el, h₁m, h₁rot, h₁out, h₁cons⟩
  rcases h₂ with ⟨h₂u, h₂e8, h₂el, h₂m, h₂rot, h₂out, h₂cons⟩
  refine And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout ?hcons)))))
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁u x hx | exact h₂u x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁e8 x hx | exact h₂e8 x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁el x hx | exact h₂el x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁m x hx | exact h₂m x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁rot x hx | exact h₂rot x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁out x hx | exact h₂out x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁cons x hx | exact h₂cons x hx

/-- Merge two verified generator packs at the same φ. -/
def VerifiedGenerators.merge {φ : ℝ} (G₁ G₂ : VerifiedGenerators φ) : VerifiedGenerators φ :=
{ C  := append G₁.C G₂.C
, ok := verified_append φ G₁.C G₂.C G₁.ok G₂.ok }

/-- Counts for a certification family. -/
@[simp] def unitsCount (C : CertFamily) : Nat := C.units.length
@[simp] def eightbeatCount (C : CertFamily) : Nat := C.eightbeat.length
@[simp] def elprobesCount (C : CertFamily) : Nat := C.elprobes.length
@[simp] def massesCount (C : CertFamily) : Nat := C.masses.length
@[simp] def rotationCount (C : CertFamily) : Nat := C.rotation.length
@[simp] def outerCount (C : CertFamily) : Nat := C.outer.length
@[simp] def consciousCount (C : CertFamily) : Nat := C.conscious.length

/-- A compact human-readable summary of a certification family. -/
@[simp] def summary (C : CertFamily) : String :=
  "units=" ++ toString (unitsCount C) ++
  ", eightbeat=" ++ toString (eightbeatCount C) ++
  ", elprobes=" ++ toString (elprobesCount C) ++
  ", masses=" ++ toString (massesCount C) ++
  ", rotation=" ++ toString (rotationCount C) ++
  ", outer=" ++ toString (outerCount C) ++
  ", conscious=" ++ toString (consciousCount C)
/-- Append two certification families by concatenating their lists. -/
def append (C₁ C₂ : CertFamily) : CertFamily :=
{ units     := C₁.units ++ C₂.units
, eightbeat := C₁.eightbeat ++ C₂.eightbeat
, elprobes  := C₁.elprobes ++ C₂.elprobes
, masses    := C₁.masses ++ C₂.masses
, rotation  := C₁.rotation ++ C₂.rotation
, outer     := C₁.outer ++ C₂.outer
, conscious := C₁.conscious ++ C₂.conscious }

/-- Verification is closed under appending certification families. -/
lemma verified_append (φ : ℝ) (C₁ C₂ : CertFamily)
  (h₁ : Verified φ C₁) (h₂ : Verified φ C₂) : Verified φ (append C₁ C₂) := by
  dsimp [Verified, append] at *
  rcases h₁ with ⟨h₁u, h₁e8, h₁el, h₁m, h₁rot, h₁out, h₁cons⟩
  rcases h₂ with ⟨h₂u, h₂e8, h₂el, h₂m, h₂rot, h₂out, h₂cons⟩
  refine And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout ?hcons)))))
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁u x hx | exact h₂u x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁e8 x hx | exact h₂e8 x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁el x hx | exact h₂el x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁m x hx | exact h₂m x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁rot x hx | exact h₂rot x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁out x hx | exact h₂out x hx
  · intro x hx; rcases List.mem_append.mp hx with hx | hx <;> first | exact h₁cons x hx | exact h₂cons x hx

end URCGenerators
end IndisputableMonolith
