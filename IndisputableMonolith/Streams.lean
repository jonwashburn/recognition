import Mathlib

namespace IndisputableMonolith

/-! #### Streams: periodic extension and finite sums -/
namespace Streams

open Classical

/-- Boolean stream as an infinite display. -/
def Stream := Nat → Bool

/-- A finite window/pattern of length `n`. -/
def Pattern (n : Nat) := Fin n → Bool

/-- Integer functional `Z` counting ones in a finite window. -/
def Z_of_window {n : Nat} (w : Pattern n) : Nat :=
  ∑ i : Fin n, (if w i then 1 else 0)

lemma Z_of_window_nonneg {n : Nat} (w : Pattern n) : 0 ≤ Z_of_window w := by
  unfold Z_of_window
  apply Finset.sum_nonneg
  intro i _
  split <;> decide

@[simp] lemma Z_of_window_zero (w : Pattern 0) : Z_of_window w = 0 := by
  simp [Z_of_window]

/-- The cylinder set of streams whose first `n` bits coincide with the window `w`. -/
def Cylinder {n : Nat} (w : Pattern n) : Set Stream :=
  { s | ∀ i : Fin n, s i.val = w i }

@[simp] lemma mem_Cylinder_zero (w : Pattern 0) (s : Stream) : s ∈ Cylinder w := by
  intro i; cases i

@[simp] lemma Cylinder_zero (w : Pattern 0) : Cylinder w = Set.univ := by
  ext s; constructor
  · intro _; exact Set.mem_univ _
  · intro _; exact mem_Cylinder_zero w s

/-- Periodic extension of an 8‑bit window. -/
def extendPeriodic8 (w : Pattern 8) : Stream := fun t =>
  let i : Fin 8 := ⟨t % 8, Nat.mod_lt _ (by decide)⟩
  w i

@[simp] lemma extendPeriodic8_zero (w : Pattern 8) : extendPeriodic8 w 0 = w ⟨0, by decide⟩ := by
  dsimp [extendPeriodic8]
  have : 0 % 8 = 0 := by decide
  simp [this]

@[simp] lemma extendPeriodic8_eq_mod (w : Pattern 8) (t : Nat) :
  extendPeriodic8 w t = w ⟨t % 8, Nat.mod_lt _ (by decide)⟩ := by
  rfl

lemma extendPeriodic8_period (w : Pattern 8) (t : Nat) :
  extendPeriodic8 w (t + 8) = extendPeriodic8 w t := by
  dsimp [extendPeriodic8]
  have hmod : (t + 8) % 8 = t % 8 := by
    simpa [Nat.mod_self, Nat.add_comm] using (Nat.add_mod t 8 8)
  have hfin : (⟨(t + 8) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)
            = ⟨t % 8, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.mk_eq_mk.mpr
    exact hmod
  simp [hfin]

/-- Period k·8: shifting by a multiple of 8 leaves `extendPeriodic8` unchanged. -/
lemma extendPeriodic8_period_k (w : Pattern 8) (t k : Nat) :
  extendPeriodic8 w (t + 8 * k) = extendPeriodic8 w t := by
  induction k with
  | zero => simpa
  | succ k ih =>
      have hrewrite : t + 8 * (Nat.succ k) = (t + 8 * k) + 8 := by
        simp [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      -- Reduce one period step, then apply the induction hypothesis.
      simpa [hrewrite, ih] using (extendPeriodic8_period w (t := t + 8 * k))

/-- Sum of the first `m` bits of a stream. -/
def sumFirst (m : Nat) (s : Stream) : Nat :=
  ∑ i : Fin m, (if s i.val then 1 else 0)

/-- Base case: the sum of the first 0 bits is 0. -/
@[simp] lemma sumFirst_zero (s : Stream) : sumFirst 0 s = 0 := by
  simp [sumFirst]

/-- If a stream agrees with a window on its first `n` bits, then the first‑`n` sum equals `Z`. -/
lemma sumFirst_eq_Z_on_cylinder {n : Nat} (w : Pattern n)
  {s : Stream} (hs : s ∈ Cylinder w) :
  sumFirst n s = Z_of_window w := by
  unfold sumFirst Z_of_window Cylinder at *
  have : (fun i : Fin n => (if s i.val then 1 else 0)) =
         (fun i : Fin n => (if w i then 1 else 0)) := by
    funext i; simpa [hs i]
  simpa [this]

/-- For an 8‑bit window extended periodically, the first‑8 sum equals `Z`. -/
lemma sumFirst8_extendPeriodic_eq_Z (w : Pattern 8) :
  sumFirst 8 (extendPeriodic8 w) = Z_of_window w := by
  unfold sumFirst Z_of_window extendPeriodic8
  have hmod : ∀ i : Fin 8, (i.val % 8) = i.val := by
    intro i; exact Nat.mod_eq_of_lt i.isLt
  refine (congrArg (fun f => ∑ i : Fin 8, f i) ?_)?_;
  · funext i; simp [hmod i]
  · rfl

/-- The sum of the first `m` bits is at most `m`. -/
lemma sumFirst_le_m (m : Nat) (s : Stream) : sumFirst m s ≤ m := by
  unfold sumFirst
  have hle : ∀ i : Fin m, (if s i.val then 1 else 0) ≤ 1 := by
    intro i; by_cases h : s i.val <;> simp [h]
  have : (∑ i : Fin m, (if s i.val then 1 else 0)) ≤ (∑ _i : Fin m, (1 : Nat)) :=
    Finset.sum_le_sum (fun i _ => hle i)
  simpa using (le_trans this (by simpa using (Finset.card_univ (α := Fin m))))

lemma extendPeriodic8_in_cylinder (w : Pattern 8) : (extendPeriodic8 w) ∈ (Cylinder w) := by
  intro i
  dsimp [extendPeriodic8, Cylinder]
  have hmod : (i.val % 8) = i.val := Nat.mod_eq_of_lt i.isLt
  simp [hmod]

lemma sumFirst_nonneg (m : Nat) (s : Stream) : 0 ≤ sumFirst m s := by
  unfold sumFirst
  apply Finset.sum_nonneg
  intro i _
  split
  · norm_num
  · norm_num

lemma sumFirst_eq_zero_of_all_false {m : Nat} {s : Stream}
  (h : ∀ i : Fin m, s i.val = false) :
  sumFirst m s = 0 := by
  unfold sumFirst
  have : (fun i : Fin m => (if s i.val then 1 else 0)) = (fun _ => 0) := by
    funext i; simp [h i]
  simp [this]

/-- If all of the first `m` bits of a stream are true, the sum is `m`. -/
lemma sumFirst_eq_m_of_all_true {m : Nat} {s : Stream}
  (h : ∀ i : Fin m, s i.val = true) :
  sumFirst m s = m := by
  unfold sumFirst
  have : (fun i : Fin m => (if s i.val then 1 else 0)) = (fun _ => (1 : Nat)) := by
    funext i; simp [h i]
  simp [this]

end Streams

end IndisputableMonolith
