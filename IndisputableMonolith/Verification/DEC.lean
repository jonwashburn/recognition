import Mathlib

namespace IndisputableMonolith

/-! ## Electromagnetism (strict bridge skeleton via DEC)
    Minimal, admit-free cochain skeleton sufficient to state Bianchi (dF=0),
    gauge invariance of F=dA, and current conservation from Ampère (d(*F)=J ⇒ dJ=0).
    This abstracts the discrete complex and avoids committing to a particular
    mesh; concrete instances provide the cochains and coboundaries. -/
namespace DEC

universe u₃

/-- Additively-written cochain space up to degree 3 with coboundaries d₀..d₃.
    The dd=0 laws are included as structure fields, so downstream lemmas are
    admit-free once an instance is provided. -/
structure CochainSpace (A : Type u) [AddCommMonoid A] where
  d0 : A → A
  d1 : A → A
  d2 : A → A
  d3 : A → A
  d0_add : ∀ x y, d0 (x + y) = d0 x + d0 y
  d1_add : ∀ x y, d1 (x + y) = d1 x + d1 y
  d2_add : ∀ x y, d2 (x + y) = d2 x + d2 y
  d3_add : ∀ x y, d3 (x + y) = d3 x + d3 y
  d0_zero : d0 0 = 0
  d1_zero : d1 0 = 0
  d2_zero : d2 0 = 0
  d3_zero : d3 0 = 0
  dd01 : ∀ x, d1 (d0 x) = 0
  dd12 : ∀ x, d2 (d1 x) = 0
  dd23 : ∀ x, d3 (d2 x) = 0

namespace CochainSpace

variable {A : Type u} [AddCommMonoid A]

/-- Field strength 2-cochain from a 1-cochain potential. -/
def F (X : CochainSpace A) (A1 : A) : A := X.d1 A1

/-- Bianchi identity (strict): dF = 0. -/
theorem bianchi (X : CochainSpace A) (A1 : A) : X.d2 (X.F A1) = 0 := by
  unfold F
  simpa using X.dd12 A1

/-- Gauge transform of the 1-cochain potential by a 0-cochain χ. -/
def gauge (X : CochainSpace A) (A1 χ : A) : A := A1 + X.d0 χ

/-- Gauge invariance: F(A + dχ) = F(A). -/
theorem F_gauge_invariant (X : CochainSpace A) (A1 χ : A) :
  X.F (X.gauge A1 χ) = X.F A1 := by
  unfold F gauge
  have h := X.d1_add A1 (X.d0 χ)
  simpa [h, X.dd01 χ]

/-- Minimal constitutive layer: a degree-preserving "Hodge" on 2-cochains. -/
structure MaxwellModel (A : Type u) [AddCommMonoid A] extends CochainSpace A where
  star2 : A → A
  star2_add : ∀ x y, star2 (x + y) = star2 x + star2 y
  star2_zero : star2 0 = 0

namespace MaxwellModel

variable {A : Type u} [AddCommMonoid A]

/-- Ampère law (DEC form): J := d(*F). -/
def J (M : MaxwellModel A) (A1 : A) : A :=
  M.d2 (M.star2 (M.d1 A1))

/-- Continuity (strict): dJ = 0 follows from dd=0. -/
theorem current_conservation (M : MaxwellModel A) (A1 : A) :
  M.d3 (M.J A1) = 0 := by
  unfold J
  simpa using M.dd23 (M.star2 (M.d1 A1))

end MaxwellModel
end CochainSpace

end DEC

/-! ## Electromagnetism (4D covariant DEC instance, typed)
    Typed 4D cochain complex C⁰..C⁴ with d₀..d₃ and dd=0, plus a Maxwell model
    with a 2-form Hodge placeholder ⋆ : C² → C². Proves Bianchi, gauge invariance,
    and current conservation in the typed setting. -/
namespace DEC4D

universe u

structure Complex4D
  (C0 C1 C2 C3 C4 : Type u)
  [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
  [AddCommMonoid C3] [AddCommMonoid C4] where
  d0 : C0 → C1
  d1 : C1 → C2
  d2 : C2 → C3
  d3 : C3 → C4
  d0_add : ∀ x y, d0 (x + y) = d0 x + d0 y
  d1_add : ∀ x y, d1 (x + y) = d1 x + d1 y
  d2_add : ∀ x y, d2 (x + y) = d2 x + d2 y
  d3_add : ∀ x y, d3 (x + y) = d3 x + d3 y
  d0_zero : d0 0 = 0
  d1_zero : d1 0 = 0
  d2_zero : d2 0 = 0
  d3_zero : d3 0 = 0
  dd01 : ∀ a, d1 (d0 a) = 0
  dd12 : ∀ a, d2 (d1 a) = 0
  dd23 : ∀ a, d3 (d2 a) = 0

namespace Complex4D

variable {C0 C1 C2 C3 C4 : Type u}
variable [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
variable [AddCommMonoid C3] [AddCommMonoid C4]

def F (X : Complex4D C0 C1 C2 C3 C4) (A : C1) : C2 := X.d1 A

theorem bianchi (X : Complex4D C0 C1 C2 C3 C4) (A : C1) :
  X.d2 (X.F A) = 0 := by
  unfold F
  simpa using X.dd12 A

def gauge (X : Complex4D C0 C1 C2 C3 C4) (A : C1) (χ : C0) : C1 := A + X.d0 χ

theorem F_gauge_invariant (X : Complex4D C0 C1 C2 C3 C4) (A : C1) (χ : C0) :
  X.F (X.gauge A χ) = X.F A := by
  unfold F gauge
  have h := X.d1_add A (X.d0 χ)
  simpa [h, X.dd01 χ]

structure MaxwellModel4D
  (C0 C1 C2 C3 C4 : Type u)
  [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
  [AddCommMonoid C3] [AddCommMonoid C4]
  extends Complex4D C0 C1 C2 C3 C4 where
  star2 : C2 → C2
  star2_add : ∀ x y, star2 (x + y) = star2 x + star2 y
  star2_zero : star2 0 = 0

namespace MaxwellModel4D

variable {C0 C1 C2 C3 C4 : Type u}
variable [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
variable [AddCommMonoid C3] [AddCommMonoid C4]

def J (M : MaxwellModel4D C0 C1 C2 C3 C4) (A : C1) : C3 :=
  M.toComplex4D.d2 (M.star2 (M.toComplex4D.d1 A))

theorem current_conservation (M : MaxwellModel4D C0 C1 C2 C3 C4) (A : C1) :
  M.toComplex4D.d3 (M.J A) = 0 := by
  unfold J
  simpa using M.toComplex4D.dd23 (M.star2 (M.toComplex4D.d1 A))

end MaxwellModel4D

/-- Trivial 4D Maxwell model builder: zero coboundaries and identity ⋆. -/
def trivial
  (C0 C1 C2 C3 C4 : Type u)
  [AddCommMonoid C0] [AddCommMonoid C1] [AddCommMonoid C2]
  [AddCommMonoid C3] [AddCommMonoid C4] :
  MaxwellModel4D C0 C1 C2 C3 C4 :=
{ d0 := fun _ => 0
, d1 := fun _ => 0
, d2 := fun _ => 0
, d3 := fun _ => 0
, d0_add := by intro x y; simp
, d1_add := by intro x y; simp
, d2_add := by intro x y; simp
, d3_add := by intro x y; simp
, d0_zero := by simp
, d1_zero := by simp
, d2_zero := by simp
, d3_zero := by simp
, dd01 := by intro a; simp
, dd12 := by intro a; simp
, dd23 := by intro a; simp
, star2 := id
, star2_add := by intro x y; rfl
, star2_zero := by rfl }

end Complex4D
end DEC4D

/-! ### Compatibility re-exports (MaxwellDEC alias)
Omitted in WIP to avoid instance inference issues. Use DEC.* and DEC4D.* directly.
-/
namespace MaxwellDEC
end MaxwellDEC

end IndisputableMonolith
