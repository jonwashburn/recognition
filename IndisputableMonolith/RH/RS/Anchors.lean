import Mathlib

namespace IndisputableMonolith
namespace RH
namespace RS

/-! Measurement anchors placeholder. -/
structure Anchors where
  a1 : ℝ
  a2 : ℝ

/-- Linear combinations of anchors (simple helper). -/
@[simp] def combine (A : Anchors) (x y : ℝ) : ℝ := x * A.a1 + y * A.a2

@[simp] lemma combine_zero_right (A : Anchors) (x : ℝ) : combine A x 0 = x * A.a1 := by
  simp [combine]

@[simp] lemma combine_zero_left (A : Anchors) (y : ℝ) : combine A 0 y = y * A.a2 := by
  simp [combine]

@[simp] lemma combine_add (A : Anchors) (x₁ x₂ y₁ y₂ : ℝ) :
  combine A (x₁ + x₂) (y₁ + y₂) = combine A x₁ y₁ + combine A x₂ y₂ := by
  simp [combine, mul_add, add_comm, add_left_comm, add_assoc]

@[simp] lemma combine_smul (A : Anchors) (a x y : ℝ) :
  combine A (a * x) (a * y) = a * combine A x y := by
  simp [combine, mul_comm, mul_left_comm, mul_assoc, left_distrib, right_distrib]

@[simp] lemma combine_sub (A : Anchors) (x₁ x₂ y₁ y₂ : ℝ) :
  combine A (x₁ - x₂) (y₁ - y₂) = combine A x₁ y₁ - combine A x₂ y₂ := by
  simp [combine, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul]

/-- If both anchors are positive and the coefficients are nonnegative, the combination is ≥ 0. -/
lemma combine_nonneg (A : Anchors) {x y : ℝ}
  (ha1 : 0 ≤ A.a1) (ha2 : 0 ≤ A.a2) (hx : 0 ≤ x) (hy : 0 ≤ y) :
  0 ≤ combine A x y := by
  dsimp [combine]
  have hx' : 0 ≤ x * A.a1 := mul_nonneg hx ha1
  have hy' : 0 ≤ y * A.a2 := mul_nonneg hy ha2
  exact add_nonneg hx' hy'

end RS
end RH
end IndisputableMonolith
