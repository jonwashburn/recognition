import Mathlib
import IndisputableMonolith.Cost

namespace IndisputableMonolith
namespace CostDemo

open Cost

noncomputable def Gcosh (t : ℝ) : ℝ := ((Real.exp t + Real.exp (-t)) / 2 - 1)

lemma Gcosh_even : ∀ t : ℝ, Gcosh (-t) = Gcosh t := by
  intro t
  simpa [Gcosh, add_comm] using rfl

lemma Gcosh_base0 : Gcosh 0 = 0 := by
  simp [Gcosh]

instance : LogModel Gcosh :=
  { even_log := Gcosh_even
  , base0 := Gcosh_base0
  , upper_cosh := by intro t; exact le_of_eq rfl
  , lower_cosh := by intro t; exact le_of_eq rfl }

/-- End-to-end T5: for x > 0, F_ofLog Gcosh x = Jcost x -/ 
theorem F_ofLog_Gcosh_eq_Jcost : ∀ {x : ℝ}, 0 < x → F_ofLog Gcosh x = Jcost x :=
  T5_for_log_model (G := Gcosh)

end CostDemo

namespace CostDemo2

open Cost

noncomputable def GcoshScaled (t : ℝ) : ℝ := (CostDemo.Gcosh t)

instance : LogModel GcoshScaled :=
  { even_log := by intro t; dsimp [GcoshScaled]; simpa using CostDemo.Gcosh_even t
  , base0 := by dsimp [GcoshScaled]; simpa using CostDemo.Gcosh_base0
  , upper_cosh := by intro t; dsimp [GcoshScaled]; exact le_of_eq rfl
  , lower_cosh := by intro t; dsimp [GcoshScaled]; exact le_of_eq rfl }

example : ∀ {x : ℝ}, 0 < x → F_ofLog GcoshScaled x = Jcost x :=
  T5_for_log_model (G := GcoshScaled)

/-- EL stationarity at 0: the first variation vanishes for `Jlog` at `t=0`. -/
@[simp] theorem EL_stationary_at_zero : deriv Jlog 0 = 0 := by
  simpa using deriv_Jlog_zero

/-- Global minimality: `t=0` is a global minimizer of `Jlog`. -/
@[simp] theorem EL_global_min (t : ℝ) : Jlog 0 ≤ Jlog t := by
  simpa [Jlog_zero] using Jlog_nonneg t

end CostDemo2

end IndisputableMonolith
