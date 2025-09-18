import Mathlib

namespace IndisputableMonolith
namespace Constants

/-- Golden ratio φ as a concrete real. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have h1 : (0 : ℝ) < 1 := by norm_num
  have hge : (1 : ℝ) ≤ 1 + Real.sqrt 5 := by
    have := h0
    have : 1 + 0 ≤ 1 + Real.sqrt 5 := add_le_add_left this 1
    simpa [one_add, add_comm] using this
  have : 0 < 1 + Real.sqrt 5 := lt_of_lt_of_le h1 hge
  have htwo : 0 < (2 : ℝ) := by norm_num
  simpa [phi] using (div_pos this htwo)

lemma one_lt_phi : 1 < phi := by
  have hroot : Real.sqrt 1 < Real.sqrt 5 := by
    simpa [Real.sqrt_one] using (Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5))
  have hsum : (1 : ℝ) + 1 < 1 + Real.sqrt 5 := add_lt_add_left hroot 1
  have htwo : 0 < (2 : ℝ) := by norm_num
  have := (div_lt_div_of_pos_right hsum htwo)
  simpa [phi, Real.sqrt_one] using this

lemma phi_ge_one : 1 ≤ phi := le_of_lt one_lt_phi
lemma phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos
lemma phi_ne_one : phi ≠ 1 := ne_of_gt one_lt_phi

/-- Minimal RS units used in Core. -/
structure RSUnits where
  tau0 : ℝ
  ell0 : ℝ
  c    : ℝ
  c_ell0_tau0 : c * tau0 = ell0

/-- Minimal global constant K placeholder. -/
@[simp] def K : ℝ := 1

lemma K_pos : 0 < K := by simp [K]
lemma K_nonneg : 0 ≤ K := by simp [K]

end Constants
end IndisputableMonolith
