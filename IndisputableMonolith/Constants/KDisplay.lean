import Mathlib
import IndisputableMonolith.Core

open IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Constants

/-! ### Dimensionless bridge ratio K and display equalities -/

namespace RSUnits

/-- Clock-side display definition: τ_rec(display) = K · τ0. -/
@[simp] noncomputable def tau_rec_display (U : RSUnits) : ℝ := K * RSUnits.tau0 U

/-- Length-side (kinematic) display definition: λ_kin(display) = K · ℓ0. -/
@[simp] noncomputable def lambda_kin_display (U : RSUnits) : ℝ := K * RSUnits.ell0 U

/-- Clock-side ratio: τ_rec(display)/τ0 = K. -/
@[simp] lemma tau_rec_display_ratio (U : RSUnits) : (tau_rec_display U) / RSUnits.tau0 U = K := by
  simp [tau_rec_display]

/-- Length-side ratio: λ_kin(display)/ℓ0 = K. -/
@[simp] lemma lambda_kin_display_ratio (U : RSUnits) : (lambda_kin_display U) / RSUnits.ell0 U = K := by
  simp [lambda_kin_display]

/-- Kinematic consistency: c · τ_rec(display) = λ_kin(display). -/
@[simp] lemma lambda_kin_from_tau_rec (U : RSUnits) : U.c * tau_rec_display U = lambda_kin_display U := by
  -- c·(K τ0) = K·(c τ0) = K·ℓ0
  have : U.c * U.tau0 = U.ell0 := U.c_ell0_tau0
  calc
    U.c * tau_rec_display U = U.c * (K * U.tau0) := by rw [tau_rec_display]
    _ = K * (U.c * U.tau0) := by ring
    _ = K * U.ell0 := by rw [this]
    _ = lambda_kin_display U := by rw [lambda_kin_display]

/-- Dimensionless bridge gate: the two independent displays agree at the ratio level. -/
@[simp] lemma K_gate (U : RSUnits) : (tau_rec_display U) / U.tau0 = (lambda_kin_display U) / U.ell0 := by
  rw [tau_rec_display_ratio, lambda_kin_display_ratio]

/-- Length-side display ratio equals K. -/
@[simp] lemma K_eq_lambda_over_ell0 (U : RSUnits) : (lambda_kin_display U) / U.ell0 = K :=
  lambda_kin_display_ratio U

/-- Clock-side display ratio equals K. -/
@[simp] lemma K_eq_tau_over_tau0 (U : RSUnits) : (tau_rec_display U) / U.tau0 = K :=
  tau_rec_display_ratio U

/-- Canonical K-gate: both route ratios equal K. -/
@[simp] theorem K_gate_eqK (U : RSUnits) :
  ((tau_rec_display U) / U.tau0 = K) ∧ ((lambda_kin_display U) / U.ell0 = K) := by
  exact ⟨tau_rec_display_ratio U, lambda_kin_display_ratio U⟩

/-- Canonical K-gate (triple form): both equal K and hence equal each other. -/
@[simp] theorem K_gate_triple (U : RSUnits) :
  ((tau_rec_display U) / U.tau0 = (lambda_kin_display U) / U.ell0)
  ∧ ((tau_rec_display U) / U.tau0 = K)
  ∧ ((lambda_kin_display U) / U.ell0 = K) := by
  exact ⟨K_gate U, tau_rec_display_ratio U, lambda_kin_display_ratio U⟩

/-- Structural speed identity from units: ℓ0/τ0 = c. -/
@[simp] lemma ell0_div_tau0_eq_c (U : RSUnits) (h : U.tau0 ≠ 0) : U.ell0 / U.tau0 = U.c := by
  rw [← U.c_ell0_tau0, mul_div_cancel_right₀ U.c U.tau0 h]

/-- Display speed equals structural speed: (λ_kin/τ_rec) = c. -/
@[simp] lemma display_speed_eq_c_of_nonzero (U : RSUnits)
  (hτ : tau_rec_display U ≠ 0) : (lambda_kin_display U) / (tau_rec_display U) = U.c := by
  -- From c * τ_rec(display) = λ_kin(display), divide both sides by τ_rec(display)
  have h := lambda_kin_from_tau_rec U
  -- Use division to isolate the ratio
  have h' := congrArg (fun x => x / tau_rec_display U) h
  -- Simplify the right-hand side using the nonzero hypothesis
  simpa [mul_div_cancel_left₀, hτ] using h'

/-! Strengthen display-speed equality: remove nonzero hypothesis by proving positivity. -/
lemma tau_rec_display_pos (U : RSUnits) (h : 0 < U.tau0) : 0 < tau_rec_display U := by
  -- K > 0 and τ0 > 0 imply K * τ0 > 0
  have hK : 0 < K := K_pos
  simpa [tau_rec_display, mul_comm] using mul_pos hK h

@[simp] lemma tau_rec_display_ne_zero (U : RSUnits) (h : 0 < U.tau0) : tau_rec_display U ≠ 0 := by
  exact ne_of_gt (tau_rec_display_pos U h)

@[simp] lemma display_speed_eq_c (U : RSUnits) (h : 0 < U.tau0) :
  (lambda_kin_display U) / (tau_rec_display U) = RSUnits.c U := by
  have hτ : tau_rec_display U ≠ 0 := tau_rec_display_ne_zero U h
  exact display_speed_eq_c_of_nonzero U hτ

end RSUnits

end Constants
end IndisputableMonolith