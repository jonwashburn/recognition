import Mathlib

namespace IndisputableMonolith
namespace CostDemo

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
