import Mathlib

namespace IndisputableMonolith
namespace Cost

noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

@[simp] lemma Jcost_exp (t : ℝ) :
  Jcost (Real.exp t) = ((Real.exp t) + (Real.exp (-t))) / 2 - 1 := by
  have h : (Real.exp t)⁻¹ = Real.exp (-t) := by
    symm; simp [Real.exp_neg t]
  simp [Jcost, h]

noncomputable def Jlog (t : ℝ) : ℝ := Jcost (Real.exp t)

@[simp] lemma Jlog_as_cosh (t : ℝ) : Jlog t = Real.cosh t - 1 := by
  dsimp [Jlog]
  simpa [Real.cosh, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (Jcost_exp t)

lemma hasDerivAt_Jlog (t : ℝ) : HasDerivAt Jlog (Real.sinh t) t := by
  have h := Real.hasDerivAt_cosh t
  have h' : HasDerivAt (fun t => Real.cosh t - 1) (Real.sinh t) t := by
    simpa [sub_eq_add_neg] using h.sub_const 1
  simpa [Jlog_as_cosh] using h'

@[simp] lemma deriv_Jlog_zero : deriv Jlog 0 = 0 := by
  classical
  have : HasDerivAt Jlog 0 0 := by simpa using (hasDerivAt_Jlog 0)
  simpa using this.deriv

@[simp] lemma Jlog_zero : Jlog 0 = 0 := by
  dsimp [Jlog]
  simp

lemma Jlog_nonneg (t : ℝ) : 0 ≤ Jlog t := by
  dsimp [Jlog]
  have h : 1 ≤ Real.cosh t := Real.cosh_ge_one t
  have : 0 ≤ Real.cosh t - 1 := sub_nonneg.mpr h
  simpa using this

end Cost

namespace CostDemo

open Cost

noncomputable def Gcosh (t : ℝ) : ℝ := ((Real.exp t + Real.exp (-t)) / 2 - 1)

lemma Gcosh_even : ∀ t : ℝ, Gcosh (-t) = Gcosh t := by
  intro t
  simpa [Gcosh, add_comm] using rfl

lemma Gcosh_base0 : Gcosh 0 = 0 := by
  simp [Gcosh]

end CostDemo

namespace CostDemo2

open Cost

noncomputable def GcoshScaled (t : ℝ) : ℝ := (CostDemo.Gcosh t)

@[simp] theorem EL_stationary_at_zero : deriv Jlog 0 = 0 := by
  simpa using deriv_Jlog_zero

@[simp] theorem EL_global_min (t : ℝ) : Jlog 0 ≤ Jlog t := by
  simpa [Jlog_zero] using Jlog_nonneg t

end CostDemo2

end IndisputableMonolith
