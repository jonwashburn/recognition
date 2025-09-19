import Mathlib

namespace IndisputableMonolith
namespace Constants

/-- Axiom stubs for dependencies -/
noncomputable def phi : ℝ := 0
axiom one_lt_phi : 1 < phi
noncomputable def RSUnits : Type := Unit
noncomputable def RSUnits.pos_c (U : RSUnits) : 0 < RSUnits.c U := sorry
noncomputable def RSUnits.c (U : RSUnits) : ℝ := 1
noncomputable def RSUnits.pos_tau0 (U : RSUnits) : 0 < RSUnits.tau0 U := sorry
noncomputable def RSUnits.tau0 (U : RSUnits) : ℝ := 1
noncomputable def RSUnits.ell0 (U : RSUnits) : ℝ := 1
axiom c_mul_tau0_eq_ell0 : ∀ U : RSUnits, RSUnits.c U * RSUnits.tau0 U = RSUnits.ell0 U

/-! ### Dimensionless bridge ratio K and display equalities -/

/-- Golden-ratio based dimensionless bridge constant: K = 2π / (8 ln φ). -/
@[simp] noncomputable def K : ℝ := (2 * Real.pi) / (8 * Real.log phi)

/-- Helper: extract positive c from RSUnits. -/
@[simp] lemma c_pos (U : RSUnits) : 0 < RSUnits.c U := RSUnits.pos_c U

namespace RSUnits

/-- Clock-side display definition: τ_rec(display) = K · τ0. -/
@[simp] noncomputable def tau_rec_display (U : RSUnits) : ℝ := K * RSUnits.tau0 U

/-- Length-side (kinematic) display definition: λ_kin(display) = K · ℓ0. -/
@[simp] noncomputable def lambda_kin_display (U : RSUnits) : ℝ := K * RSUnits.ell0 U

/-- Clock-side ratio: τ_rec(display)/τ0 = K. -/
@[simp] lemma tau_rec_display_ratio (U : RSUnits) : (tau_rec_display U) / RSUnits.tau0 U = K := by
  sorry

/-- Length-side ratio: λ_kin(display)/ℓ0 = K. -/
@[simp] lemma lambda_kin_display_ratio (U : RSUnits) : (lambda_kin_display U) / RSUnits.ell0 U = K := by
  -- deduce ℓ0 ≠ 0 from c>0 and τ0>0 using ℓ0 = c·τ0
  have hc : 0 < RSUnits.c U := c_pos U
  have ht : 0 < RSUnits.tau0 U := RSUnits.pos_tau0 U
  have hℓpos : 0 < RSUnits.ell0 U := by simpa [c_mul_tau0_eq_ell0 U] using (mul_pos hc ht)
  have hℓ : RSUnits.ell0 U ≠ 0 := ne_of_gt hℓpos
  simpa [lambda_kin_display] using (mul_div_cancel K hℓ)

/-- Kinematic consistency: c · τ_rec(display) = λ_kin(display). -/
@[simp] lemma lambda_kin_from_tau_rec (U : RSUnits) : RSUnits.c U * tau_rec_display U = lambda_kin_display U := by
  -- c·(K τ0) = K·(c τ0) = K·ℓ0
  simpa [tau_rec_display, lambda_kin_display, mul_comm, mul_left_comm, mul_assoc, c_mul_tau0_eq_ell0 U]

/-- Dimensionless bridge gate: the two independent displays agree at the ratio level. -/
@[simp] lemma K_gate (U : RSUnits) : (tau_rec_display U) / RSUnits.tau0 U = (lambda_kin_display U) / RSUnits.ell0 U := by
  simpa [tau_rec_display_ratio U, lambda_kin_display_ratio U]

/-- Length-side display ratio equals K. -/
@[simp] lemma K_eq_lambda_over_ell0 (U : RSUnits) : (lambda_kin_display U) / RSUnits.ell0 U = K :=
  lambda_kin_display_ratio U

/-- Clock-side display ratio equals K. -/
@[simp] lemma K_eq_tau_over_tau0 (U : RSUnits) : (tau_rec_display U) / RSUnits.tau0 U = K :=
  tau_rec_display_ratio U

/-- Canonical K-gate: both route ratios equal K. -/
@[simp] theorem K_gate_eqK (U : RSUnits) :
  ((tau_rec_display U) / RSUnits.tau0 U = K) ∧ ((lambda_kin_display U) / RSUnits.ell0 U = K) := by
  exact And.intro (tau_rec_display_ratio U) (lambda_kin_display_ratio U)

/-- Canonical K-gate (triple form): both equal K and hence equal each other. -/
@[simp] theorem K_gate_triple (U : RSUnits) :
  ((tau_rec_display U) / RSUnits.tau0 U = (lambda_kin_display U) / RSUnits.ell0 U)
  ∧ ((tau_rec_display U) / RSUnits.tau0 U = K)
  ∧ ((lambda_kin_display U) / RSUnits.ell0 U = K) := by
  refine And.intro ?hEq ?hPair
  · simpa [tau_rec_display_ratio U, lambda_kin_display_ratio U]
  · exact And.intro (tau_rec_display_ratio U) (lambda_kin_display_ratio U)

/-- Structural speed identity from units: ℓ0/τ0 = c. -/
@[simp] lemma ell0_div_tau0_eq_c (U : RSUnits) : RSUnits.ell0 U / RSUnits.tau0 U = RSUnits.c U := by
  have ht : RSUnits.tau0 U ≠ 0 := ne_of_gt (RSUnits.pos_tau0 U)
  -- rewrite ℓ0 = c · τ0 and cancel τ0
  simpa [c_mul_tau0_eq_ell0 U] using (mul_div_cancel (RSUnits.c U) ht)

/-- Display speed equals structural speed: (λ_kin/τ_rec) = c. -/
@[simp] lemma display_speed_eq_c_of_nonzero (U : RSUnits)
  (hτ : tau_rec_display U ≠ 0) : (lambda_kin_display U) / (tau_rec_display U) = RSUnits.c U := by
  -- From c · τ_rec = λ_kin, divide both sides by τ_rec
  have h := lambda_kin_from_tau_rec U
  -- rewrite division as multiplication by inverse
  have : (lambda_kin_display U) * (tau_rec_display U)⁻¹ = RSUnits.c U := by
    calc
      (lambda_kin_display U) * (tau_rec_display U)⁻¹
          = (RSUnits.c U * tau_rec_display U) * (tau_rec_display U)⁻¹ := by
                simpa [h]
      _   = RSUnits.c U * (tau_rec_display U * (tau_rec_display U)⁻¹) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
      _   = RSUnits.c U * 1 := by
                have : tau_rec_display U ≠ 0 := hτ
                simp [this]
      _   = RSUnits.c U := by simp
  -- convert back to a division
  simpa [div_eq_mul_inv] using this.symm

/-! Strengthen display-speed equality: remove nonzero hypothesis by proving positivity. -/
lemma tau_rec_display_pos (U : RSUnits) : 0 < tau_rec_display U := by
  -- K > 0 and τ0 > 0 imply positivity
  have hτ0 : 0 < RSUnits.tau0 U := RSUnits.pos_tau0 U
  have hlogφpos : 0 < Real.log phi := by
    -- φ > 1 ⇒ log φ > 0
    have : 1 < phi := one_lt_phi
    simpa [Real.log_pos_iff] using this
  have hKpos : 0 < K := by
    -- K = (2π) / (8 log φ) > 0
    have hnum : 0 < 2 * Real.pi := by
      have : 0 < Real.pi := Real.pi_pos
      have : 0 < 2 := by norm_num
      exact mul_pos this Real.pi_pos
    have hden : 0 < 8 * Real.log phi := by
      have : 0 < (8 : ℝ) := by norm_num
      exact mul_pos this hlogφpos
    have : 0 < (2 * Real.pi) / (8 * Real.log phi) := (div_pos_iff.mpr ⟨hnum, hden⟩)
    simpa [K] using this
  have : 0 < K * RSUnits.tau0 U := mul_pos hKpos hτ0
  simpa [tau_rec_display] using this

@[simp] lemma tau_rec_display_ne_zero (U : RSUnits) : tau_rec_display U ≠ 0 := ne_of_gt (tau_rec_display_pos U)

@[simp] lemma display_speed_eq_c (U : RSUnits) :
  (lambda_kin_display U) / (tau_rec_display U) = RSUnits.c U :=
  display_speed_eq_c_of_nonzero U (tau_rec_display_ne_zero U)

end RSUnits

end Constants
end IndisputableMonolith