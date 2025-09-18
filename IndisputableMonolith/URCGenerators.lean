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

/-- Add a mass certificate to a certification family. -/
def consMass (c : MassCert) (C : CertFamily) : CertFamily :=
{ C with masses := c :: C.masses }

/-- If a mass certificate is verified and the family is verified, the augmented family is verified. -/
lemma verified_consMass (φ : ℝ) (c : MassCert) (C : CertFamily)
  (hc : MassCert.verified φ c) (hC : Verified φ C) : Verified φ (consMass c C) := by
  dsimp [Verified, consMass] at *
  rcases hC with ⟨hU, hE8, hEL, hM, hRot, hOut, hCons⟩
  refine And.intro ?hU (And.intro ?hE8 (And.intro ?hEL (And.intro ?hM (And.intro ?hRot (And.intro ?hOut ?hCons)))))
  · intro x hx; exact hU x hx
  · intro x hx; exact hE8 x hx
  · intro x hx; exact hEL x hx
  · intro x hx
    -- masses is `c :: C.masses`
    rcases List.mem_cons.mp hx with hx | hx
    · simpa [hx]
    · exact hM x hx
  · intro x hx; exact hRot x hx
  · intro x hx; exact hOut x hx
  · intro x hx; exact hCons x hx

/-- Add a units certificate to a certification family. -/
def consUnits (c : UnitsCert) (C : CertFamily) : CertFamily :=
{ C with units := c :: C.units }

lemma verified_consUnits (φ : ℝ) (c : UnitsCert) (C : CertFamily)
  (hc : UnitsCert.verified c) (hC : Verified φ C) : Verified φ (consUnits c C) := by
  dsimp [Verified, consUnits] at *
  rcases hC with ⟨hU, hE8, hEL, hM, hRot, hOut, hCons⟩
  refine And.intro ?hU' (And.intro ?hE8 (And.intro ?hEL (And.intro ?hM (And.intro ?hRot (And.intro ?hOut ?hCons)))))
  · intro x hx; rcases List.mem_cons.mp hx with hx | hx
    · simpa [hx]
    · exact hU x hx
  · intro x hx; exact hE8 x hx
  · intro x hx; exact hEL x hx
  · intro x hx; exact hM x hx
  · intro x hx; exact hRot x hx
  · intro x hx; exact hOut x hx
  · intro x hx; exact hCons x hx

/-- Add an eight-beat certificate to a certification family. -/
def consEightBeat (c : EightBeatCert) (C : CertFamily) : CertFamily :=
{ C with eightbeat := c :: C.eightbeat }

lemma verified_consEightBeat (φ : ℝ) (c : EightBeatCert) (C : CertFamily)
  (hc : EightBeatCert.verified c) (hC : Verified φ C) : Verified φ (consEightBeat c C) := by
  dsimp [Verified, consEightBeat] at *
  rcases hC with ⟨hU, hE8, hEL, hM, hRot, hOut, hCons⟩
  refine And.intro ?hU (And.intro ?hE8' (And.intro ?hEL (And.intro ?hM (And.intro ?hRot (And.intro ?hOut ?hCons)))))
  · intro x hx; exact hU x hx
  · intro x hx; rcases List.mem_cons.mp hx with hx | hx
    · simpa [hx]
    · exact hE8 x hx
  · intro x hx; exact hEL x hx
  · intro x hx; exact hM x hx
  · intro x hx; exact hRot x hx
  · intro x hx; exact hOut x hx
  · intro x hx; exact hCons x hx

/-- Add an EL probe certificate to a certification family. -/
def consELProbe (c : ELProbe) (C : CertFamily) : CertFamily :=
{ C with elprobes := c :: C.elprobes }

lemma verified_consELProbe (φ : ℝ) (c : ELProbe) (C : CertFamily)
  (hc : ELProbe.verified c) (hC : Verified φ C) : Verified φ (consELProbe c C) := by
  dsimp [Verified, consELProbe] at *
  rcases hC with ⟨hU, hE8, hEL, hM, hRot, hOut, hCons⟩
  refine And.intro ?hU (And.intro ?hE8 (And.intro ?hEL' (And.intro ?hM (And.intro ?hRot (And.intro ?hOut ?hCons)))))
  · intro x hx; exact hU x hx
  · intro x hx; exact hE8 x hx
  · intro x hx; rcases List.mem_cons.mp hx with hx | hx
    · simpa [hx]
    · exact hEL x hx
  · intro x hx; exact hM x hx
  · intro x hx; exact hRot x hx
  · intro x hx; exact hOut x hx
  · intro x hx; exact hCons x hx

/-- Filter mass certificates by a predicate; keep other lists unchanged. -/
def filterMasses (p : MassCert → Bool) (C : CertFamily) : CertFamily :=
{ C with masses := C.masses.filter p }

lemma verified_filterMasses (φ : ℝ) (p : MassCert → Bool) (C : CertFamily)
  (hC : Verified φ C) : Verified φ (filterMasses p C) := by
  dsimp [Verified, filterMasses] at *
  rcases hC with ⟨hU, hE8, hEL, hM, hRot, hOut, hCons⟩
  refine And.intro ?hU (And.intro ?hE8 (And.intro ?hEL (And.intro ?hM' (And.intro ?hRot (And.intro ?hOut ?hCons)))))
  · intro x hx; exact hU x hx
  · intro x hx; exact hE8 x hx
  · intro x hx; exact hEL x hx
  · intro x hx
    -- x ∈ filter p C.masses implies x ∈ C.masses
    have hx' : x ∈ C.masses := by
      exact List.of_mem_filter hx
    exact hM x hx'
  · intro x hx; exact hRot x hx
  · intro x hx; exact hOut x hx
  · intro x hx; exact hCons x hx

/-- Add a rotation certificate to a certification family. -/
def consRotation (c : RotationCert) (C : CertFamily) : CertFamily :=
{ C with rotation := c :: C.rotation }

lemma verified_consRotation (φ : ℝ) (c : RotationCert) (C : CertFamily)
  (hc : RotationCert.verified c) (hC : Verified φ C) : Verified φ (consRotation c C) := by
  dsimp [Verified, consRotation] at *
  rcases hC with ⟨hU, hE8, hEL, hM, hRot, hOut, hCons⟩
  refine And.intro ?hU (And.intro ?hE8 (And.intro ?hEL (And.intro ?hM (And.intro ?hRot' (And.intro ?hOut ?hCons)))))
  · intro x hx; exact hU x hx
  · intro x hx; exact hE8 x hx
  · intro x hx; exact hEL x hx
  · intro x hx; exact hM x hx
  · intro x hx; rcases List.mem_cons.mp hx with hx | hx
    · simpa [hx]
    · exact hRot x hx
  · intro x hx; exact hOut x hx
  · intro x hx; exact hCons x hx

/-- Add an outer-budget certificate to a certification family. -/
def consOuter (c : OuterBudgetCert) (C : CertFamily) : CertFamily :=
{ C with outer := c :: C.outer }

lemma verified_consOuter (φ : ℝ) (c : OuterBudgetCert) (C : CertFamily)
  (hc : OuterBudgetCert.verified c) (hC : Verified φ C) : Verified φ (consOuter c C) := by
  dsimp [Verified, consOuter] at *
  rcases hC with ⟨hU, hE8, hEL, hM, hRot, hOut, hCons⟩
  refine And.intro ?hU (And.intro ?hE8 (And.intro ?hEL (And.intro ?hM (And.intro ?hRot (And.intro ?hOut' ?hCons)))))
  · intro x hx; exact hU x hx
  · intro x hx; exact hE8 x hx
  · intro x hx; exact hEL x hx
  · intro x hx; exact hM x hx
  · intro x hx; exact hRot x hx
  · intro x hx; rcases List.mem_cons.mp hx with hx | hx
    · simpa [hx]
    · exact hOut x hx
  · intro x hx; exact hCons x hx

/-- Add a conscious certificate to a certification family. -/
def consConscious (c : ConsciousCert) (C : CertFamily) : CertFamily :=
{ C with conscious := c :: C.conscious }

lemma verified_consConscious (φ : ℝ) (c : ConsciousCert) (C : CertFamily)
  (hc : ConsciousCert.verified c) (hC : Verified φ C) : Verified φ (consConscious c C) := by
  dsimp [Verified, consConscious] at *
  rcases hC with ⟨hU, hE8, hEL, hM, hRot, hOut, hCons⟩
  refine And.intro ?hU (And.intro ?hE8 (And.intro ?hEL (And.intro ?hM (And.intro ?hRot (And.intro ?hOut ?hCons')))))
  · intro x hx; exact hU x hx
  · intro x hx; exact hE8 x hx
  · intro x hx; exact hEL x hx
  · intro x hx; exact hM x hx
  · intro x hx; exact hRot x hx
  · intro x hx; exact hOut x hx
  · intro x hx; rcases List.mem_cons.mp hx with hx | hx
    · simpa [hx]
    · exact hCons x hx

/-- Empty certification family constant. -/
@[simp] def emptyFamily : CertFamily :=
{ units := [], eightbeat := [], elprobes := [], masses := []
, rotation := [], outer := [], conscious := [] }

/-- Fold-append a list of certification families. -/
@[simp] def foldAppend (fs : List CertFamily) : CertFamily :=
  fs.foldl append emptyFamily

lemma verified_foldl_append (φ : ℝ) (fs : List CertFamily)
  (h : ∀ C ∈ fs, Verified φ C) : Verified φ (foldAppend fs) := by
  induction fs with
  | nil => simpa [foldAppend, emptyFamily] using (verified_empty φ)
  | cons C fs ih =>
      have hC  : Verified φ C := h C (by simp)
      have hfs : Verified φ (foldAppend fs) :=
        ih (by intro X hX; exact h X (by simpa [List.mem_cons] using Or.inr hX))
      -- foldl step: (C :: fs).foldl append emptyFamily = append C (foldAppend fs)
      simpa [foldAppend, List.foldl] using (verified_append φ C (foldAppend fs) hC hfs)

/-- Cert family with a single units certificate. -/
@[simp] def singletonUnitsFamily (c : UnitsCert) : CertFamily :=
{ units := [c], eightbeat := [], elprobes := [], masses := []
, rotation := [], outer := [], conscious := [] }

lemma verified_singletonUnits (φ : ℝ) (c : UnitsCert)
  (h : UnitsCert.verified c) : Verified φ (singletonUnitsFamily c) := by
  dsimp [Verified, singletonUnitsFamily]
  refine And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout ?hcons)))))
  · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx

/-- Cert family with a single eight-beat certificate. -/
@[simp] def singletonEightBeatFamily (c : EightBeatCert) : CertFamily :=
{ units := [], eightbeat := [c], elprobes := [], masses := []
, rotation := [], outer := [], conscious := [] }

lemma verified_singletonEightBeat (φ : ℝ) (c : EightBeatCert)
  (h : EightBeatCert.verified c) : Verified φ (singletonEightBeatFamily c) := by
  dsimp [Verified, singletonEightBeatFamily]
  refine And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout ?hcons)))))
  · intro x hx; cases hx
  · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx

/-- Cert family with a single EL probe. -/
@[simp] def singletonELProbeFamily (c : ELProbe) : CertFamily :=
{ units := [], eightbeat := [], elprobes := [c], masses := []
, rotation := [], outer := [], conscious := [] }

lemma verified_singletonELProbe (φ : ℝ) (c : ELProbe)
  (h : ELProbe.verified c) : Verified φ (singletonELProbeFamily c) := by
  dsimp [Verified, singletonELProbeFamily]
  refine And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout ?hcons)))))
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; rcases List.mem_singleton.mp hx with rfl; exact h
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
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
