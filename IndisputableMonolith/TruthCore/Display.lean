import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith

namespace Constants

@[simp] noncomputable def RSUnits.tau_rec_display (U : RSUnits) : ℝ := K * U.tau0
@[simp] noncomputable def RSUnits.lambda_kin_display (U : RSUnits) : ℝ := K * U.ell0
axiom RSUnits.display_speed_eq_c (U : RSUnits) :
  (RSUnits.lambda_kin_display U) / (RSUnits.tau_rec_display U) = U.c

end Constants

namespace TruthCore

/-- Alias: display speed identity λ_kin/τ_rec = c. -/
theorem display_speed_identity (U : Constants.RSUnits) :
  (Constants.RSUnits.lambda_kin_display U) / (Constants.RSUnits.tau_rec_display U) = U.c :=
  Constants.RSUnits.display_speed_eq_c U

end TruthCore

end IndisputableMonolith
