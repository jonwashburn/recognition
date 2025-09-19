import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.MaxwellDEC
import IndisputableMonolith.Gap45

namespace IndisputableMonolith
namespace Verification

open Constants

/-- Export: DEC d∘d=0 for cochains. -/
theorem dec_dd_eq_zero {A} (X : MaxwellDEC.CochainSpace A) :
  (∀ a, X.d1 (X.d0 a) = 0) ∧ (∀ b, X.d2 (X.d1 b) = 0) := by
  exact ⟨(by intro a; simpa using X.dd01 a), (by intro b; simpa using X.dd12 b)⟩

/-- Export: Bianchi identity dF=0. -/
theorem dec_bianchi {A} (X : MaxwellDEC.CochainSpace A) (A1 : A) :
  MaxwellDEC.CochainSpace.d2 X (MaxwellDEC.CochainSpace.F X A1) = 0 := by
  simpa using MaxwellDEC.CochainSpace.bianchi X A1

/-- Export: display speed identity λ_kin/τ_rec = c. -/
theorem display_speed_identity (U : Constants.RSUnits) :
  (Constants.RSUnits.lambda_kin_display U) / (Constants.RSUnits.tau_rec_display U) = U.c := by
  simpa using Constants.RSUnits.display_speed_eq_c U

/-- Export: 45-gap clock-lag fraction identity (dimensionless): δ_time = 3/64. -/
theorem gap_delta_time_identity : (45 : ℚ) / 960 = (3 : ℚ) / 64 := by
  simpa using Gap45.delta_time_eq_3_div_64

end Verification
end IndisputableMonolith


