import Mathlib

namespace IndisputableMonolith
namespace Constants

/-- Golden ratio φ as a concrete real. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have hge : (1 : ℝ) ≤ 1 + Real.sqrt 5 := by
    have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    simpa using add_le_add_left hs 1
  have : 0 < 1 + Real.sqrt 5 := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hge
  have htwo : 0 < (2 : ℝ) := by norm_num
  simpa [phi] using (div_pos this htwo)

lemma one_lt_phi : 1 < phi := by
  have hroot : Real.sqrt 1 < Real.sqrt 5 := by
    simpa [Real.sqrt_one] using (Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5))
  have hsum : (1 : ℝ) + 1 < 1 + Real.sqrt 5 := by
    simpa [Real.sqrt_one] using (add_lt_add_left hroot 1)
  have htwo : 0 < (2 : ℝ) := by norm_num
  have := (div_lt_div_of_pos_right hsum htwo)
  simpa [phi, Real.sqrt_one] using this

/-‑ φ^2 = φ + 1. -/
lemma phi_squared : phi ^ 2 = phi + 1 := by
  -- Expand ((1+√5)/2)^2 and simplify
  have : phi ^ 2 = ((1 + Real.sqrt 5) ^ 2) / 4 := by
    have := by ring
    simpa [phi, this]
  have hsq : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
    have : (1 + Real.sqrt 5) ^ 2 = 1 + 2 * Real.sqrt 5 + (Real.sqrt 5) ^ 2 := by ring
    have : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
      have : 0 ≤ (5 : ℝ) := by norm_num
      simpa [pow_two] using Real.sqrt_mul_self this
    simpa [this] using by
      have : 1 + 2 * Real.sqrt 5 + 5 = 6 + 2 * Real.sqrt 5 := by ring
      simpa [this]
  have : phi ^ 2 = (6 + 2 * Real.sqrt 5) / 4 := by simpa [hsq] using this
  -- Also φ + 1 = (3+√5)/2
  have : phi + 1 = (3 + Real.sqrt 5) / 2 := by
    have : (1 + Real.sqrt 5) / 2 + 1 = ((1 + Real.sqrt 5) + 2) / 2 := by ring
    simpa [phi] using this
  -- Show (6 + 2√5)/4 = (3 + √5)/2
  have : (6 + 2 * Real.sqrt 5) / 4 = (3 + Real.sqrt 5) / 2 := by
    ring
  simpa [this] using this

/-‑ φ = 1 + 1/φ. -/
lemma phi_fixed_point : phi = 1 + 1 / phi := by
  have hne : phi ≠ 0 := ne_of_gt phi_pos
  have hsq : phi ^ 2 = phi + 1 := phi_squared
  have := congrArg (fun x => x / phi) hsq
  simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

-- (Optional stronger facts about φ can be added later if needed.)

lemma phi_ge_one : 1 ≤ phi := le_of_lt one_lt_phi
lemma phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos
lemma phi_ne_one : phi ≠ 1 := ne_of_gt one_lt_phi

/-- Minimal RS units used in Core. -/
structure RSUnits where
  tau0 : ℝ
  ell0 : ℝ
  c    : ℝ
  c_ell0_tau0 : c * tau0 = ell0

/-- If τ0 ≠ 0, the units identity `c·τ0 = ℓ0` yields `c = ℓ0/τ0`. -/
lemma RSUnits.c_eq_ell0_div_tau0 (U : RSUnits) (hτ : U.tau0 ≠ 0) :
  U.c = U.ell0 / U.tau0 := by
  -- a = b/τ ↔ a*τ = b
  exact ( (eq_div_iff_mul_eq (by exact hτ)).mpr U.c_ell0_tau0 )

/-- If τ0 ≠ 0, the units identity `c·τ0 = ℓ0` yields `ℓ0/τ0 = c`. -/
lemma RSUnits.ell0_div_tau0_eq_c (U : RSUnits) (hτ : U.tau0 ≠ 0) :
  U.ell0 / U.tau0 = U.c := by
  simpa [RSUnits.c_eq_ell0_div_tau0 U hτ] using (RSUnits.c_eq_ell0_div_tau0 U hτ).symm

/-- Minimal global constant K placeholder. -/
@[simp] def K : ℝ := 1

lemma K_pos : 0 < K := by simp [K]
lemma K_nonneg : 0 ≤ K := by simp [K]

/-! Stable RS display wrappers (dependency-light) -/
namespace RSUnits

@[simp] noncomputable def tau_rec_display (U : RSUnits) : ℝ := K * U.tau0

@[simp] noncomputable def lambda_kin_display (U : RSUnits) : ℝ := K * U.ell0

@[simp] lemma tau_rec_display_ratio (U : RSUnits) (hτ : U.tau0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = K := by
  simp [tau_rec_display, hτ]

@[simp] lemma lambda_kin_display_ratio (U : RSUnits) (hℓ : U.ell0 ≠ 0) :
  (lambda_kin_display U) / U.ell0 = K := by
  simp [lambda_kin_display, hℓ]

@[simp] lemma lambda_kin_from_tau_rec (U : RSUnits) :
  U.c * tau_rec_display U = lambda_kin_display U := by
  simp [tau_rec_display, lambda_kin_display, U.c_ell0_tau0,
        mul_comm, mul_left_comm, mul_assoc]

    lemma tau_rec_display_pos (U : RSUnits) (hτ : 0 < U.tau0) :
      0 < tau_rec_display U := by
      have hK : 0 < K := K_pos
      simpa [tau_rec_display, mul_comm, mul_left_comm, mul_assoc]
        using mul_pos hK hτ

    lemma lambda_kin_display_pos (U : RSUnits) (hℓ : 0 < U.ell0) :
      0 < lambda_kin_display U := by
      have hK : 0 < K := K_pos
      simpa [lambda_kin_display, mul_comm, mul_left_comm, mul_assoc]
        using mul_pos hK hℓ

end RSUnits

end Constants
end IndisputableMonolith
