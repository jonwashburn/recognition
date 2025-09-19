import Mathlib

namespace IndisputableMonolith
namespace Causality

/-! Minimal local interfaces to avoid heavy imports during WIP standalone check. -/

class BoundedStep (α : Type) (degree_bound : outParam Nat) where
  step : α → α → Prop
  neighbors : α → Finset α
  step_iff_mem : ∀ x y, step x y ↔ y ∈ neighbors x
  degree_bound_holds : ∀ x, (neighbors x).card ≤ degree_bound

structure Kinematics (α : Type) where
  step : α → α → Prop

/-- `ballP K x n y` means y is within ≤ n steps of x via `K.step`. -/
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

@[simp] lemma mem_ballFS_zero {x y : α} : y ∈ ballFS (α:=α) x 0 ↔ y = x := by
  classical
  constructor
  · intro hy; simpa [ballFS, Finset.mem_singleton] using hy
  · intro hxy; simpa [ballFS, Finset.mem_singleton, hxy]

@[simp] lemma mem_bind_neighbors {s : Finset α} {y : α} :
  y ∈ s.biUnion (fun z => B.neighbors z) ↔ ∃ z ∈ s, y ∈ B.neighbors z := by
  classical
  constructor
  · intro hy; rcases Finset.mem_biUnion.mp hy with ⟨z, hz, hyNz⟩; exact ⟨z, hz, hyNz⟩
  · intro h; rcases h with ⟨z, hz, hyNz⟩; exact Finset.mem_biUnion.mpr ⟨z, hz, hyNz⟩

theorem mem_ballFS_iff_ballP (x y : α) : ∀ n, y ∈ ballFS (α:=α) x n ↔ ballP (KB (α:=α)) x n y := by
  classical
  intro n; induction' n with n ih generalizing y
  · simpa [ballFS, ballP]
  · constructor
    · intro hy
      dsimp [ballFS] at hy
      rcases Finset.mem_union.mp hy with hyPrev | hyExp
      · exact Or.inl ((ih y).mp hyPrev)
      · rcases Finset.mem_biUnion.mp hyExp with ⟨z, hzPrev, hyNz⟩
        have hBstep : B.step z y := (B.step_iff_mem (x:=z) (y:=y)).mpr hyNz
        have hKstep : (KB (α:=α)).step z y := by simpa [KB] using hBstep
        exact Or.inr ⟨z, (ih z).mp hzPrev, hKstep⟩
    · intro hy
      dsimp [ballP] at hy; dsimp [ballFS]
      cases hy with
      | inl hyPrev => exact Finset.mem_union.mpr (Or.inl ((ih y).mpr hyPrev))
      | inr hyStep =>
          rcases hyStep with ⟨z, hzPrev, hKstep⟩
          have hBstep : B.step z y := by simpa [KB] using hKstep
          have hyNz : y ∈ B.neighbors z := (B.step_iff_mem (x:=z) (y:=y)).mp hBstep
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨z, (ih z).mpr hzPrev, hyNz⟩))

@[simp] lemma card_singleton {x : α} : ({x} : Finset α).card = 1 := by
  classical
  simp

lemma card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card := by
  classical
  have : (s ∪ t).card ≤ (s ∪ t).card + (s ∩ t).card := Nat.le_add_right _ _
  simpa [Finset.card_union_add_card_inter] using this

lemma card_bind_le_sum (s : Finset α) (f : α → Finset α) :
  (s.biUnion f).card ≤ Finset.sum s (fun z => (f z).card) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hbind : (insert a s).biUnion f = f a ∪ s.biUnion f := by
      classical
      ext x
      simp [Finset.mem_biUnion, Finset.mem_insert, ha, Finset.mem_union]
    have hle : ((insert a s).biUnion f).card ≤ (f a).card + (s.biUnion f).card := by
      simpa [hbind] using card_union_le (f a) (s.biUnion f)
    have hsum : (f a).card + (s.biUnion f).card ≤ Finset.sum (insert a s) (fun z => (f z).card) := by
      simpa [Finset.sum_insert, ha] using Nat.add_le_add_left ih ((f a).card)
    exact le_trans hle hsum

lemma sum_card_neighbors_le (s : Finset α) :
  Finset.sum s (fun z => (B.neighbors z).card) ≤ d * s.card := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hdeg : (B.neighbors a).card ≤ d := B.degree_bound_holds a
    have : Finset.sum (insert a s) (fun z => (B.neighbors z).card)
          = (B.neighbors a).card + Finset.sum s (fun z => (B.neighbors z).card) := by
      simp [Finset.sum_insert, ha]
    have hle : (B.neighbors a).card + Finset.sum s (fun z => (B.neighbors z).card)
               ≤ d + Finset.sum s (fun z => (B.neighbors z).card) := Nat.add_le_add_right hdeg _
    have hmul : d + Finset.sum s (fun z => (B.neighbors z).card) ≤ d * (s.card + 1) := by
      have := ih
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_one] using
        (Nat.add_le_add_left this d)
    have : Finset.sum (insert a s) (fun z => (B.neighbors z).card) ≤ d * (insert a s).card := by
      simpa [this, Finset.card_insert_of_not_mem ha, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (le_trans hle hmul)
    exact this

lemma card_bind_neighbors_le (s : Finset α) :
  (s.biUnion (fun z => B.neighbors z)).card ≤ d * s.card := by
  classical
  exact le_trans (card_bind_le_sum (s := s) (f := fun z => B.neighbors z)) (sum_card_neighbors_le (s := s))

lemma card_ballFS_succ_le (x : α) (n : Nat) :
  (ballFS (α:=α) x (n+1)).card ≤ (1 + d) * (ballFS (α:=α) x n).card := by
  classical
  have : ballFS (α:=α) x (Nat.succ n) =
    let prev := ballFS (α:=α) x n
    prev ∪ prev.biUnion (fun z => B.neighbors z) := by rfl
  dsimp [ballFS] at this
  let prev := ballFS (α:=α) x n
  have h_union_le : (prev ∪ prev.biUnion (fun z => B.neighbors z)).card
                    ≤ (ballFS (α:=α) x n).card + (((ballFS (α:=α) x n).biUnion (fun z => B.neighbors z))).card := by
    simpa [ballFS, prev] using card_union_le (ballFS (α:=α) x n) ((ballFS (α:=α) x n).biUnion (fun z => B.neighbors z))
  have h_bind_le : ((ballFS (α:=α) x n).biUnion (fun z => B.neighbors z)).card
                    ≤ d * (ballFS (α:=α) x n).card := card_bind_neighbors_le (s := ballFS (α:=α) x n)
  have : (ballFS (α:=α) x (Nat.succ n)).card ≤ (ballFS (α:=α) x n).card + d * (ballFS (α:=α) x n).card := by
    simpa [this, prev] using Nat.le_trans h_union_le (Nat.add_le_add_left h_bind_le _)
  simpa [Nat.mul_add, Nat.one_mul, Nat.add_comm] using this

theorem ballFS_card_le_geom (x : α) : ∀ n : Nat, (ballFS (α:=α) x n).card ≤ (1 + d) ^ n := by
  classical
  intro n; induction' n with n ih
  · simpa [ballFS, card_singleton] using (Nat.le_of_eq (by simp : (1 + d) ^ 0 = 1))
  · have hrec := card_ballFS_succ_le (α:=α) (d:=d) (x := x) (n := n)
    have hmul : (1 + d) * (ballFS (α:=α) x n).card ≤ (1 + d) * (1 + d) ^ n := by
      exact Nat.mul_le_mul_left _ ih
    have hmul' : (1 + d) * (ballFS (α:=α) x n).card ≤ (1 + d) ^ (n+1) := by
      simpa [pow_succ, Nat.mul_comm] using hmul
    exact le_trans hrec hmul'

end ConeBound
end Causality
end IndisputableMonolith

import Mathlib

namespace IndisputableMonolith

namespace Causality

variable {α : Type}

structure Kinematics (α : Type) where
  step : α → α → Prop

inductive ReachN (K : Kinematics α) : Nat → α → α → Prop
| zero {x} : ReachN K 0 x x
| succ {n x y z} : ReachN K n x y → K.step y z → ReachN K (n+1) x z

/-- Predicate n-ball: within ≤ n steps from x. -/
def ballP (K : Kinematics α) (x : α) : Nat → α → Prop
| 0, y => y = x
| Nat.succ n, y => ballP K x n y ∨ ∃ z, ballP K x n z ∧ K.step z y

lemma ballP_mono {K : Kinematics α} {x : α} {n m : Nat}
  (hnm : n ≤ m) : {y | ballP K x n y} ⊆ {y | ballP K x m y} := by
  induction hnm with
  | refl => intro y hy; simpa using hy
  | @step m hm ih =>
      intro y hy; exact Or.inl (ih hy)

lemma reach_mem_ballP {K : Kinematics α} {x y : α} :
  ∀ {n}, ReachN K n x y → ballP K x n y := by
  intro n h; induction h with
  | zero => simp [ballP]
  | @succ n x y z hxy hyz ih => exact Or.inr ⟨y, ih, hyz⟩

end Causality

/-- Locally-finite step relation with bounded out-degree. -/
class BoundedStep (α : Type) (degree_bound : outParam Nat) where
  step : α → α → Prop
  neighbors : α → Finset α
  step_iff_mem : ∀ x y, step x y ↔ y ∈ neighbors x
  degree_bound_holds : ∀ x, (neighbors x).card ≤ degree_bound

namespace ConeBound

open Causality
open scoped BigOperators

variable {α : Type} {d : Nat}
variable [DecidableEq α]
variable [B : BoundedStep α d]

/-- Kinematics induced by a `BoundedStep` instance. -/
def KB : Kinematics α := { step := B.step }

/-- Finset n-ball via BFS expansion using `neighbors`. -/
noncomputable def ballFS (x : α) : Nat → Finset α
| 0 => {x}
| Nat.succ n =>
    let prev := ballFS x n
    prev ∪ prev.biUnion (fun z => B.neighbors z)

@[simp] lemma mem_ballFS_zero {x y : α} : y ∈ ballFS (α:=α) x 0 ↔ y = x := by
  classical
  constructor
  · intro hy; simpa [ballFS, Finset.mem_singleton] using hy
  · intro hxy; simpa [ballFS, Finset.mem_singleton, hxy]

@[simp] lemma mem_bind_neighbors {s : Finset α} {y : α} :
  y ∈ s.biUnion (fun z => B.neighbors z) ↔ ∃ z ∈ s, y ∈ B.neighbors z := by
  classical
  constructor
  · intro hy; rcases Finset.mem_biUnion.mp hy with ⟨z, hz, hyNz⟩; exact ⟨z, hz, hyNz⟩
  · intro h; rcases h with ⟨z, hz, hyNz⟩; exact Finset.mem_biUnion.mpr ⟨z, hz, hyNz⟩

/-- BFS ball membership coincides with the logical n-ball predicate `ballP`. -/
theorem mem_ballFS_iff_ballP (x y : α) : ∀ n, y ∈ ballFS (α:=α) x n ↔ Causality.ballP (KB (α:=α)) x n y := by
  classical
  intro n
  induction' n with n ih generalizing y
  · simpa [ballFS, Causality.ballP]
  · constructor
    · intro hy
      dsimp [ballFS] at hy
      rcases Finset.mem_union.mp hy with hyPrev | hyExp
      · exact Or.inl ((ih y).mp hyPrev)
      · rcases Finset.mem_biUnion.mp hyExp with ⟨z, hzPrev, hyNz⟩
        have hBstep : B.step z y := (B.step_iff_mem (x:=z) (y:=y)).mpr hyNz
        have hKstep : (KB (α:=α)).step z y := by simpa [KB] using hBstep
        exact Or.inr ⟨z, (ih z).mp hzPrev, hKstep⟩
    · intro hy
      dsimp [Causality.ballP] at hy
      dsimp [ballFS]
      cases hy with
      | inl hyPrev => exact Finset.mem_union.mpr (Or.inl ((ih y).mpr hyPrev))
      | inr hyStep =>
          rcases hyStep with ⟨z, hz, hKstep⟩
          have hBstep : B.step z y := by simpa [KB] using hKstep
          have hyNz : y ∈ B.neighbors z := (B.step_iff_mem (x:=z) (y:=y)).mp hBstep
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨z, (ih z).mpr hz, hyNz⟩))

@[simp] lemma card_singleton {x : α} : ({x} : Finset α).card = 1 := by
  classical
  simp

/-- Cardinality inequality for unions: `|s ∪ t| ≤ |s| + |t|`. -/
lemma card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card := by
  classical
  have : (s ∪ t).card ≤ (s ∪ t).card + (s ∩ t).card := Nat.le_add_right _ _
  simpa [Finset.card_union_add_card_inter] using this

/-- Generic upper bound: the size of `s.biUnion f` is at most the sum of the sizes. -/
lemma card_bind_le_sum (s : Finset α) (f : α → Finset α) :
  (s.biUnion f).card ≤ Finset.sum s (fun z => (f z).card) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hbind : (insert a s).biUnion f = f a ∪ s.biUnion f := by
      classical; ext x; simp [Finset.mem_biUnion, Finset.mem_insert, ha, Finset.mem_union]
    have hle : ((insert a s).biUnion f).card ≤ (f a).card + (s.biUnion f).card := by
      simpa [hbind] using card_union_le (f a) (s.biUnion f)
    have hsum : (f a).card + (s.biUnion f).card ≤ Finset.sum (insert a s) (fun z => (f z).card) := by
      simpa [Finset.sum_insert, ha] using Nat.add_le_add_left ih ((f a).card)
    exact le_trans hle hsum

/-- Sum of neighbor set sizes is bounded by degree times the number of sources. -/
lemma sum_card_neighbors_le (s : Finset α) :
  Finset.sum s (fun z => (B.neighbors z).card) ≤ d * s.card := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hdeg : (B.neighbors a).card ≤ d := B.degree_bound_holds a
    have : Finset.sum (insert a s) (fun z => (B.neighbors z).card)
          = (B.neighbors a).card + Finset.sum s (fun z => (B.neighbors z).card) := by
      simp [Finset.sum_insert, ha]
    have hle : (B.neighbors a).card + Finset.sum s (fun z => (B.neighbors z).card)
               ≤ d + Finset.sum s (fun z => (B.neighbors z).card) := Nat.add_le_add_right hdeg _
    have hmul : d + Finset.sum s (fun z => (B.neighbors z).card) ≤ d * (s.card + 1) := by
      have := ih
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_one] using
        (Nat.add_le_add_left this d)
    have : Finset.sum (insert a s) (fun z => (B.neighbors z).card) ≤ d * (insert a s).card := by
      simpa [this, Finset.card_insert_of_not_mem ha, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (le_trans hle hmul)
    exact this

/-- Bound the expansion layer size: `|s.biUnion neighbors| ≤ d * |s|`. -/
lemma card_bind_neighbors_le (s : Finset α) :
  (s.biUnion (fun z => B.neighbors z)).card ≤ d * s.card := by
  classical
  exact le_trans (card_bind_le_sum (s := s) (f := fun z => B.neighbors z)) (sum_card_neighbors_le (s := s))

/-- Recurrence: `|ballFS x (n+1)| ≤ (1 + d) * |ballFS x n|`. -/
lemma card_ballFS_succ_le (x : α) (n : Nat) :
  (ballFS (α:=α) x (n+1)).card ≤ (1 + d) * (ballFS (α:=α) x n).card := by
  classical
  have : ballFS (α:=α) x (Nat.succ n) =
    let prev := ballFS (α:=α) x n
    prev ∪ prev.biUnion (fun z => B.neighbors z) := by rfl
  dsimp [ballFS] at this
  let prev := ballFS (α:=α) x n
  have h_union_le : (prev ∪ prev.biUnion (fun z => B.neighbors z)).card
                    ≤ (ballFS (α:=α) x n).card + (ballFS (α:=α) x n).biUnion (fun z => B.neighbors z) |>.card := by
    simpa [ballFS, prev] using card_union_le (ballFS (α:=α) x n) ((ballFS (α:=α) x n).biUnion (fun z => B.neighbors z))
  have h_bind_le : ((ballFS (α:=α) x n).biUnion (fun z => B.neighbors z)).card
                    ≤ d * (ballFS (α:=α) x n).card := card_bind_neighbors_le (s := ballFS (α:=α) x n)
  have : (ballFS (α:=α) x (Nat.succ n)).card ≤ (ballFS (α:=α) x n).card + d * (ballFS (α:=α) x n).card := by
    simpa [this, prev] using Nat.le_trans h_union_le (Nat.add_le_add_left h_bind_le _)
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.one_mul] using this

/-- Geometric bound: `|ballFS x n| ≤ (1 + d)^n`. -/
theorem ballFS_card_le_geom (x : α) : ∀ n : Nat, (ballFS (α:=α) x n).card ≤ (1 + d) ^ n := by
  classical
  intro n
  induction' n with n ih
  · simpa [ballFS, card_singleton] using (Nat.le_of_eq (by simp : (1 + d) ^ 0 = 1))
  · have hrec := card_ballFS_succ_le (α:=α) (d:=d) (x := x) (n := n)
    have hmul : (1 + d) * (ballFS (α:=α) x n).card ≤ (1 + d) * (1 + d) ^ n := by
      exact Nat.mul_le_mul_left _ ih
    exact le_trans hrec hmul

end ConeBound
end IndisputableMonolith

-- cleaned: use local stubs only; standalone WIP
