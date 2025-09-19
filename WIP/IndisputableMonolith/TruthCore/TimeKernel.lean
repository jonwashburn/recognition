import Mathlib
import IndisputableMonolith.Gravity.ILG

namespace IndisputableMonolith
namespace TruthCore

/-- Local alias to ILG's ratio to ensure standalone compile. -/
@[simp] def w_time_ratio (Tdyn τ0 : ℝ) : ℝ :=
  IndisputableMonolith.Gravity.ILG.w_time_ratio Tdyn τ0

lemma w_time_ratio_rescale (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_time_ratio (c * Tdyn) (c * τ0) = w_time_ratio Tdyn τ0 := by
  dsimp [w_time_ratio]
  simpa using IndisputableMonolith.Gravity.ILG.w_time_ratio_rescale (c:=c) (Tdyn:=Tdyn) (τ0:=τ0) hc

/-- Alias: time-kernel ratio is dimensionless (invariant under common rescaling). -/
theorem time_kernel_dimensionless (c T τ : ℝ) (hc : 0 < c) :
  w_time_ratio (c * T) (c * τ) = w_time_ratio T τ := by
  simpa using w_time_ratio_rescale (c:=c) (Tdyn:=T) (τ0:=τ) hc

end TruthCore
end IndisputableMonolith


