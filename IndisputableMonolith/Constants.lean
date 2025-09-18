import Mathlib

namespace IndisputableMonolith
namespace Constants

/-- Golden ratio φ as a concrete real. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have h1 : (0 : ℝ) < 1 := by norm_num
  have hge : (1 : ℝ) ≤ 1 + Real.sqrt 5 := by
    have := h0
    have : 1 + 0 ≤ 1 + Real.sqrt 5 := add_le_add_left this 1
    simpa [one_add, add_comm] using this
  have : 0 < 1 + Real.sqrt 5 := lt_of_lt_of_le h1 hge
  have htwo : 0 < (2 : ℝ) := by norm_num
  simpa [phi] using (div_pos this htwo)

lemma one_lt_phi : 1 < phi := by
  have hroot : Real.sqrt 1 < Real.sqrt 5 := by
    simpa [Real.sqrt_one] using (Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5))
  have hsum : (1 : ℝ) + 1 < 1 + Real.sqrt 5 := add_lt_add_left hroot 1
  have htwo : 0 < (2 : ℝ) := by norm_num
  have := (div_lt_div_of_pos_right hsum htwo)
  simpa [phi, Real.sqrt_one] using this

/-‑ φ^2 = φ + 1. -/
lemma phi_squared : phi ^ 2 = phi + 1 := by
  -- ((1+√5)/2)^2 = (1 + 2√5 + 5) / 4 = (6 + 2√5)/4 = (3+√5)/2 = φ + 1
  have hsq : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
    have : (1 + Real.sqrt 5) ^ 2 = 1 + 2 * Real.sqrt 5 + (Real.sqrt 5) ^ 2 := by ring
    have : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
      have : 0 ≤ (5 : ℝ) := by norm_num
      simpa [pow_two] using Real.sqrt_mul_self this
    simpa [this] using by
      have : 1 + 2 * Real.sqrt 5 + 5 = 6 + 2 * Real.sqrt 5 := by ring
      simpa [this]
  have : phi ^ 2 = ((1 + Real.sqrt 5) ^ 2) / 4 := by
    have : ((1 + Real.sqrt 5) / 2) ^ 2 = ((1 + Real.sqrt 5) ^ 2) / (2 ^ 2) := by
      field_simp [pow_two]
    simpa [phi, pow_two, this, two_mul, mul_comm, mul_left_comm, mul_assoc]
  have : phi ^ 2 = (6 + 2 * Real.sqrt 5) / 4 := by simpa [hsq] using this
  have : phi + 1 = (3 + Real.sqrt 5) / 2 := by
    have : (1 + Real.sqrt 5) / 2 + 1 = ((1 + Real.sqrt 5) + 2) / 2 := by field_simp
    simpa [phi, add_comm, add_left_comm, add_assoc] using this
  -- Show (6 + 2√5)/4 = (3 + √5)/2
  have : (6 + 2 * Real.sqrt 5) / 4 = (3 + Real.sqrt 5) / 2 := by
    field_simp
  simpa [this] using this

/-‑ φ = 1 + 1/φ. -/
lemma phi_fixed_point : phi = 1 + 1 / phi := by
  have hne : phi ≠ 0 := phi_ne_zero
  have hsq : phi ^ 2 = phi + 1 := phi_squared
  -- Divide both sides by φ
  have := congrArg (fun x => x / phi) hsq
  -- (φ^2)/φ = (φ+1)/φ ⇒ φ = 1 + 1/φ
  simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

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
  exact (eq_div_iff_mul_eq.mpr U.c_ell0_tau0)

/-- If τ0 ≠ 0, the units identity `c·τ0 = ℓ0` yields `ℓ0/τ0 = c`. -/
lemma RSUnits.ell0_div_tau0_eq_c (U : RSUnits) (hτ : U.tau0 ≠ 0) :
  U.ell0 / U.tau0 = U.c := by
  simpa [RSUnits.c_eq_ell0_div_tau0 U hτ] using (RSUnits.c_eq_ell0_div_tau0 U hτ).symm

/-- Minimal global constant K placeholder. -/
@[simp] def K : ℝ := 1

lemma K_pos : 0 < K := by simp [K]
lemma K_nonneg : 0 ≤ K := by simp [K]

end Constants
end IndisputableMonolith
