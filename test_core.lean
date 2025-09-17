import Mathlib

def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

lemma goldenRatio_pos : 0 < goldenRatio := by
  have hnum : 0 < (1 : ℝ) + Real.sqrt 5 := by
    have hroot : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  have hden : 0 < (2 : ℝ) := by norm_num
  have : 0 < (1 + Real.sqrt 5) / 2 := div_pos hnum hden
  simpa [goldenRatio] using this

#eval goldenRatio
