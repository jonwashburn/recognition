import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace RH
namespace RS
namespace Scales

/-- Affine map from ℤ to ℝ: n ↦ slope·n + offset. -/
structure AffineMapZ where
  slope : ℝ
  offset : ℝ

@[simp] def apply (f : AffineMapZ) (n : ℤ) : ℝ := f.slope * (n : ℝ) + f.offset

/-- Map δ-subgroup to ℝ by composing an affine map with the projection to ℤ. -/
noncomputable def mapDelta (δ : ℤ) (hδ : δ ≠ 0) (toZ : {x : ℤ // ∃ n : ℤ, x = n * δ} → ℤ)
  (f : AffineMapZ) : {x : ℤ // ∃ n : ℤ, x = n * δ} → ℝ :=
  fun p => f.slope * ((toZ p) : ℝ) + f.offset

/-- Context constructors: charge (quantum `qe`), time (τ0), and action (ħ). -/
@[simp] def chargeMap (qe : ℝ) : AffineMapZ := { slope := qe, offset := 0 }
@[simp] def timeMap (U : Constants.RSUnits) : AffineMapZ := { slope := U.tau0, offset := 0 }
@[simp] def actionMap (U : Constants.RSUnits) : AffineMapZ := { slope := U.hbar, offset := 0 }

end Scales
end RS
end RH
end IndisputableMonolith
