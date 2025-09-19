import Mathlib
import IndisputableMonolith.LightCone.StepBounds
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace ConeExport

variable {α : Type _}
variable (K : LightCone.Local.Kinematics α)
variable (U : Constants.RSUnits)
variable (time rad : α → ℝ)

/-- Verification-level cone bound: if per-step bounds hold, any `n`-step reach obeys
    `rad y - rad x ≤ U.c * (time y - time x)` with no `n` in the statement. -/
theorem cone_bound_export
  (H : LightCone.StepBounds K U time rad)
  {n x y} (h : LightCone.Local.ReachN K n x y) :
  rad y - rad x ≤ U.c * (time y - time x) := by
  simpa using (LightCone.StepBounds.cone_bound (K:=K) (U:=U) (time:=time) (rad:=rad) H h)

end ConeExport
end IndisputableMonolith
