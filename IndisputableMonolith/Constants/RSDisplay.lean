import Mathlib
import IndisputableMonolith.Core

/-!
RS Units Display Functions and K-Gate Theorems

This module contains the dimensionless display functions for RS units
and the fundamental K-gate theorems that establish the bridge consistency.

Note: Using axiom stubs for dependency-light extraction.
-/

namespace IndisputableMonolith.Constants.RSUnits

/-- Clock-side display definition: τ_rec(display) = K · τ0. -/
noncomputable def tau_rec_display (U : IndisputableMonolith.Constants.RSUnits) : ℝ :=
  IndisputableMonolith.Constants.K * U.tau0

/-- Length-side (kinematic) display definition: λ_kin(display) = K · ℓ0. -/
noncomputable def lambda_kin_display (U : IndisputableMonolith.Constants.RSUnits) : ℝ :=
  IndisputableMonolith.Constants.K * U.ell0

/-- Clock-side ratio: τ_rec(display)/τ0 = K. -/
@[simp] lemma tau_rec_display_ratio (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K := by
  dsimp [tau_rec_display]
  simpa using (mul_div_cancel_left₀ IndisputableMonolith.Constants.K U.tau0 hτ)

/-- Length-side ratio: λ_kin(display)/ℓ0 = K. -/
@[simp] lemma lambda_kin_display_ratio (U : IndisputableMonolith.Constants.RSUnits)
  (hℓ : U.ell0 ≠ 0) :
  (lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K := by
  dsimp [lambda_kin_display]
  simpa using (mul_div_cancel_left₀ IndisputableMonolith.Constants.K U.ell0 hℓ)

/-- Kinematic consistency: c · τ_rec(display) = λ_kin(display). -/
@[simp] lemma lambda_kin_from_tau_rec (U : IndisputableMonolith.Constants.RSUnits) :
  U.c * tau_rec_display U = lambda_kin_display U := by
  -- c·(K τ0) = K·(c τ0) = K·ℓ0
  dsimp [tau_rec_display, lambda_kin_display]
  -- use structural identity from RSUnits
  simpa [mul_comm, mul_left_comm, mul_assoc, (U.c_ell0_tau0)]

/-- Dimensionless bridge gate: the two independent displays agree at the ratio level. -/
@[simp] lemma K_gate (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = (lambda_kin_display U) / U.ell0 := by
  simpa [tau_rec_display_ratio U hτ, lambda_kin_display_ratio U hℓ]

/-- Length-side display ratio equals K. -/
@[simp] lemma K_eq_lambda_over_ell0 (U : IndisputableMonolith.Constants.RSUnits)
  (hℓ : U.ell0 ≠ 0) :
  (lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K :=
  lambda_kin_display_ratio U hℓ

/-- Clock-side display ratio equals K. -/
@[simp] lemma K_eq_tau_over_tau0 (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K :=
  tau_rec_display_ratio U hτ

/-- Canonical K-gate: both route ratios equal K. -/
@[simp] theorem K_gate_eqK (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  ((tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K) ∧
  ((lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K) := by
  exact And.intro (tau_rec_display_ratio U hτ) (lambda_kin_display_ratio U hℓ)

/-- Canonical K-gate (triple form): both equal K and hence equal each other. -/
@[simp] theorem K_gate_triple (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  ((tau_rec_display U) / U.tau0 = (lambda_kin_display U) / U.ell0)
  ∧ ((tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K)
  ∧ ((lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K) := by
  refine And.intro ?hEq (And.intro ?hTau ?hLambda)
  · exact K_gate U hτ hℓ
  · exact tau_rec_display_ratio U hτ
  · exact lambda_kin_display_ratio U hℓ

/-- Structural speed identity from units: ℓ0/τ0 = c. -/
@[simp] lemma ell0_div_tau0_eq_c (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) :
  U.ell0 / U.tau0 = U.c := by
  have : U.ell0 = U.c * U.tau0 := U.c_ell0_tau0
  simpa [this, div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using rfl

/-- Display speed equals structural speed: (λ_kin/τ_rec) = c. -/
@[simp] lemma display_speed_eq_c_of_nonzero (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : tau_rec_display U ≠ 0) : (lambda_kin_display U) / (tau_rec_display U) = U.c := by
  have h := lambda_kin_from_tau_rec U
  have h' := congrArg (fun x => x / tau_rec_display U) h
  simpa [mul_div_cancel_left₀, hτ] using h'

/-- Strengthen display-speed equality: remove nonzero hypothesis by proving positivity. -/
lemma tau_rec_display_pos (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : 0 < U.tau0) : 0 < tau_rec_display U := by
  have hK : 0 < IndisputableMonolith.Constants.K := IndisputableMonolith.Constants.K_pos
  simpa [tau_rec_display, mul_comm] using mul_pos hK hτ

@[simp] lemma tau_rec_display_ne_zero (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : 0 < U.tau0) :
  tau_rec_display U ≠ 0 := ne_of_gt (tau_rec_display_pos U hτ)

@[simp] lemma display_speed_eq_c (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : 0 < U.tau0) :
  (lambda_kin_display U) / (tau_rec_display U) = U.c :=
  display_speed_eq_c_of_nonzero U (tau_rec_display_ne_zero U hτ)

end IndisputableMonolith.Constants.RSUnits