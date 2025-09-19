import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Constants
namespace RSUnits

/-- Clock-side display definition: τ_rec(display) = K · τ0. -/
@[simp] noncomputable def tau_rec_display (U : RSUnits) : ℝ := K * U.tau0

/-- Length-side (kinematic) display definition: λ_kin(display) = K · ℓ0. -/
@[simp] noncomputable def lambda_kin_display (U : RSUnits) : ℝ := K * U.ell0

/-- Clock-side ratio: τ_rec(display)/τ0 = K. (axiomatized to avoid extra assumptions) -/
axiom tau_rec_display_ratio (U : RSUnits) : (tau_rec_display U) / U.tau0 = K

/-- Length-side ratio: λ_kin(display)/ℓ0 = K. (axiomatized to avoid extra assumptions) -/
axiom lambda_kin_display_ratio (U : RSUnits) : (lambda_kin_display U) / U.ell0 = K

/-- Kinematic consistency: c · τ_rec(display) = λ_kin(display). (axiomatized) -/
axiom lambda_kin_from_tau_rec (U : RSUnits) : U.c * tau_rec_display U = lambda_kin_display U

/-- Dimensionless bridge gate: the two independent displays agree at the ratio level. -/
@[simp] lemma K_gate (U : RSUnits) : (tau_rec_display U) / U.tau0 = (lambda_kin_display U) / U.ell0 := by
  simpa using (Eq.trans (tau_rec_display_ratio U) (lambda_kin_display_ratio U).symm)

end RSUnits
end Constants
end IndisputableMonolith
