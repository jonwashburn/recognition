import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Constants

noncomputable @[simp] def alpha_locked : ℝ := (1 - 1 / phi) / 2

noncomputable @[simp] def Clag : ℝ := 1 / (phi ^ (5 : Nat))

lemma alpha_locked_pos : 0 < alpha_locked := by
  have hφ : 1 < phi := one_lt_phi
  have hlt : 1 / phi < 1 := by
    have hφpos : 0 < phi := phi_pos
    exact (inv_lt_one_iff_of_pos hφpos).mpr hφ
  have : 0 < 1 - 1 / phi := sub_pos.mpr hlt
  have htwo : 0 < (2 : ℝ) := by norm_num
  exact div_pos this htwo

lemma alpha_locked_lt_one : alpha_locked < 1 := by
  have hhalf : (1 - 1 / phi) / 2 < (1 : ℝ) / 2 := by
    have : 1 - 1 / phi < 1 := by
      have hφpos : 0 < phi := phi_pos
      have : 0 < 1 / phi := inv_pos.mpr hφpos
      simpa using sub_lt_iff_lt_add'.mpr this
    have htwo : 0 < (2 : ℝ) := by norm_num
    exact (div_lt_div_of_pos_right this htwo)
  have : (1 : ℝ) / 2 < 1 := by norm_num
  exact lt_trans hhalf this

lemma Clag_pos : 0 < Clag := by
  have hφ : 0 < phi := phi_pos
  have hpow : 0 < phi ^ (5 : Nat) := pow_pos hφ 5
  simpa [Clag, one_div] using inv_pos.mpr hpow

end Constants
end IndisputableMonolith


