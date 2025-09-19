import Mathlib

namespace IndisputableMonolith
namespace Cost

noncomputable def Jlog (t : ℝ) : ℝ := Real.cosh t - 1

@[simp] lemma Jlog_as_cosh (t : ℝ) : Jlog t = Real.cosh t - 1 := rfl

lemma hasDerivAt_Jlog (t : ℝ) : HasDerivAt Jlog (Real.sinh t) t := by
  have h := Real.hasDerivAt_cosh t
  simpa [Jlog, sub_eq_add_neg] using h.sub_const 1

@[simp] lemma hasDerivAt_Jlog_zero : HasDerivAt Jlog 0 0 := by
  simpa using (hasDerivAt_Jlog 0)

@[simp] lemma deriv_Jlog_zero : deriv Jlog 0 = 0 := by
  classical
  simpa using (hasDerivAt_Jlog_zero).deriv

@[simp] lemma Jlog_zero : Jlog 0 = 0 := by
  simp [Jlog]

lemma Jlog_nonneg (t : ℝ) : 0 ≤ Jlog t := by
  have h : 1 ≤ Real.cosh t := Real.cosh_ge_one t
  have : 0 ≤ Real.cosh t - 1 := sub_nonneg.mpr h
  simpa [Jlog] using this

lemma Jlog_eq_zero_iff (t : ℝ) : Jlog t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have : Real.cosh t = 1 := by simpa [Jlog] using congrArg (fun x => x + 1) h
    simpa using (Real.cosh_eq_one_iff.mp this)
  · intro ht; subst ht; simp [Jlog]

end Cost
end IndisputableMonolith


