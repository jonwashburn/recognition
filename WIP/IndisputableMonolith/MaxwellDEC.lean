import Mathlib

namespace IndisputableMonolith
namespace MaxwellDEC

/-- Oriented k-simplex (abstract id). -/
structure Simplex (α : Type) (k : Nat) where
  id     : α
  orient : Bool

/-- Discrete k-form: value per oriented k-simplex. -/
@[simp] def DForm (α : Type) (k : Nat) := Simplex α k → ℝ

/-- Coboundary operator interface on the mesh. -/
class HasCoboundary (α : Type) where
  d : ∀ {k : Nat}, DForm α k → DForm α (k+1)

/-- Hodge star interface (metric/constitutive). -/
class HasHodge (α : Type) where
  n : Nat
  star : ∀ {k : Nat}, DForm α k → DForm α (n - k)

/-- Linear medium parameters. -/
structure Medium (α : Type) [HasHodge α] where
  eps : ℝ
  mu  : ℝ

/-- Sources (charge and current). -/
structure Sources (α : Type) where
  ρ : DForm α 0
  J : DForm α 1

variable {α : Type}

/-- Quasi-static Maxwell equations on the mesh (no time derivative terms). -/
structure Equations (α : Type) [HasCoboundary α] [HasHodge α] (M : Medium α) where
  E : DForm α 1
  H : DForm α 1
  B : DForm α 2
  D : DForm α 2
  src : Sources α
  faraday_qs : True
  ampere_qs  : True
  gauss_e    : True
  gauss_m    : True
  const_D    : True
  const_B    : True

/-- PEC boundary descriptor (edges where tangential E vanishes). -/
structure PEC (β : Type) where
  boundary1 : Set (Simplex β 1)

end MaxwellDEC
end IndisputableMonolith
