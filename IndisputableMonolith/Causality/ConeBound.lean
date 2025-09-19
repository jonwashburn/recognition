import Mathlib

namespace IndisputableMonolith
namespace Causality

/-! WIP minimal ConeBound: local stubs to avoid project imports. -/

class BoundedStep (α : Type) (degree_bound : outParam Nat) where
  step : α → α → Prop
  neighbors : α → Finset α
  step_iff_mem : ∀ x y, step x y ↔ y ∈ neighbors x
  degree_bound_holds : ∀ x, (neighbors x).card ≤ degree_bound

structure Kinematics (α : Type) where
  step : α → α → Prop

def ballP (K : Kinematics α) (x : α) : Nat → α → Prop
| 0, y => y = x
| Nat.succ n, y => ballP K x n y ∨ ∃ z, ballP K x n z ∧ K.step z y

namespace ConeBound

variable {α : Type} {d : Nat}
variable [DecidableEq α]
variable [B : BoundedStep α d]

def KB : Kinematics α := { step := B.step }

noncomputable def ballFS (x : α) : Nat → Finset α
| 0 => {x}
| Nat.succ n =>
    let prev := ballFS x n
    prev ∪ prev.biUnion (fun z => B.neighbors z)

axiom mem_ballFS_iff_ballP (x y : α) : ∀ n, y ∈ ballFS (α:=α) x n ↔ ballP (KB (α:=α)) x n y
theorem card_singleton {x : α} : ({x} : Finset α).card = 1 :=
  Finset.card_singleton x
theorem card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card :=
  Finset.card_union_le s t
theorem card_bind_le_sum (s : Finset α) (f : α → Finset α) :
  (s.biUnion f).card ≤ Finset.sum s (fun z => (f z).card) :=
  Finset.card_biUnion_le_sum s f
theorem sum_card_neighbors_le (s : Finset α) :
  Finset.sum s (fun z => (B.neighbors z).card) ≤ d * s.card := by
  apply Finset.sum_le_sum
  intro z hz
  exact B.degree_bound_holds z
theorem card_bind_neighbors_le (s : Finset α) :
  (s.biUnion (fun z => B.neighbors z)).card ≤ d * s.card := by
  have h1 := card_bind_le_sum s (fun z => B.neighbors z)
  have h2 := sum_card_neighbors_le s
  exact Nat.le_trans h1 h2
axiom card_ballFS_succ_le (x : α) (n : Nat) :
  (ballFS (α:=α) x (n+1)).card ≤ (1 + d) * (ballFS (α:=α) x n).card
axiom ballFS_card_le_geom (x : α) : ∀ n : Nat, (ballFS (α:=α) x n).card ≤ (1 + d) ^ n

end ConeBound
end Causality
end IndisputableMonolith
