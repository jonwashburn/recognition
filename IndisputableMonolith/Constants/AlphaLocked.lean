import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Constants

@[simp] noncomputable def alpha_locked : ℝ := (1 - 1 / phi) / 2
@[simp] noncomputable def Clag : ℝ := 1 / (phi ^ (5 : Nat))

lemma alpha_locked_pos : 0 < alpha_locked := by
  have hφ : 1 < phi := one_lt_phi
  have hlt : 1 / phi < 1 := by
    have h0 : 0 < (1 : ℝ) := by norm_num
    have : 1 / phi < 1 / 1 := one_div_lt_one_div_of_lt h0 hφ
    simpa [one_div] using this
  have : 0 < 1 - 1 / phi := sub_pos.mpr hlt
  have htwo : 0 < (2 : ℝ) := by norm_num
  exact div_pos this htwo

lemma alpha_locked_lt_one : alpha_locked < 1 := by
  have hlt : (1 - 1 / phi) / 2 < (1 : ℝ) / 2 := by
    have hpos : 0 < 1 / phi := by
      have := inv_pos.mpr phi_pos
      simpa [one_div] using this
    have : 1 - 1 / phi < 1 := by linarith
    have htwo : 0 < (2 : ℝ) := by norm_num
    exact div_lt_div_of_pos_right this htwo
  have : (1 : ℝ) / 2 < 1 := by norm_num
  exact lt_trans hlt this

lemma Clag_pos : 0 < Clag := by
  have hpow : 0 < phi ^ (5 : Nat) := pow_pos phi_pos 5
  simpa [Clag, one_div] using inv_pos.mpr hpow

end Constants
end IndisputableMonolith


