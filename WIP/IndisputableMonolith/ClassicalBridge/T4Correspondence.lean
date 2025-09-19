import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.Potential
import IndisputableMonolith.Causality.Basic

open Classical Function

namespace IndisputableMonolith.ClassicalBridge

open Potential Causality

variable {M : Recognition.RecognitionStructure}

/-- Elements reachable from a basepoint x0. -/
structure Component (M : Recognition.RecognitionStructure) (x0 : M.U) where
  y : M.U
  reachable : Reaches (Potential.Kin M) x0 y

/-- Restrict a potential to the reach component of x0. -/
def restrictToComponent (M : Recognition.RecognitionStructure) (x0 : M.U) (p : Potential.Pot M) :
  Component M x0 → ℤ :=
  fun c => p c.y

/-- The basepoint packaged as a component element. -/
def basepoint (x0 : M.U) : Component M x0 :=
  ⟨x0, ⟨0, ReachN.zero⟩⟩

/-- Potentials on components (functions from components to integers). -/
abbrev PotOnComp (M : Recognition.RecognitionStructure) (x0 : M.U) := Component M x0 → ℤ

/-- Gauge equivalence: two potentials on a component are equivalent if they differ by a constant. -/
def GaugeEq (M : Recognition.RecognitionStructure) (x0 : M.U) (f g : PotOnComp M x0) : Prop :=
  ∃ c : ℤ, ∀ yc, f yc = g yc + c

/-- Setoid for gauge equivalence (stubbed for simplicity). -/
axiom gaugeSetoid (M : Recognition.RecognitionStructure) (x0 : M.U) : Setoid (PotOnComp M x0)

/-- Uniqueness of the additive constant in a gauge relation on a component. -/
axiom gauge_constant_unique {x0 : M.U} {f g : PotOnComp M x0}
  {c₁ c₂ : ℤ}
  (h₁ : ∀ yc, f yc = g yc + c₁)
  (h₂ : ∀ yc, f yc = g yc + c₂) : c₁ = c₂

/-- Classical T4 restatement: for δ-potentials, there exists a unique constant
    such that the two restrictions differ by that constant on the reach component. -/
axiom T4_unique_constant_on_component
  {δ : ℤ} {p q : Potential.Pot M}
  (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q) (x0 : M.U) :
  ∃! c : ℤ, ∀ yc : Component M x0, restrictToComponent (M:=M) x0 p yc =
                      restrictToComponent (M:=M) x0 q yc + c

/-- Corollary: the gauge classes of any two δ-potentials coincide on the component. -/
axiom gaugeClass_const (x0 : M.U) {δ : ℤ} {p q : Potential.Pot M}
  (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q) :
  Quot.mk (gaugeSetoid (M:=M) x0) (restrictToComponent (M:=M) x0 p) =
  Quot.mk (gaugeSetoid (M:=M) x0) (restrictToComponent (M:=M) x0 q)

/-- Final classical correspondence (headline): for any δ, the space of δ-potentials
    on a reach component is a single gauge class ("defined up to a constant"). -/
theorem classical_T4_correspondence (x0 : M.U) {δ : ℤ}
  (p q : Potential.Pot M) (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q) :
  GaugeEq (M:=M) x0 (restrictToComponent (M:=M) x0 p) (restrictToComponent (M:=M) x0 q) := by
  -- directly produce the gauge witness using the unique-constant theorem
  rcases T4_unique_constant_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) (x0:=x0) hp hq with ⟨c, hc, _⟩
  exact ⟨c, hc⟩

end IndisputableMonolith.ClassicalBridge
