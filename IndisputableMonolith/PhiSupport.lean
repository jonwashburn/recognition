import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace PhiSupport

/-- φ^2 = φ + 1 using the closed form φ = (1+√5)/2. -/
@[simp] theorem phi_squared : Constants.phi ^ 2 = Constants.phi + 1 := by
  -- Expand ((1+√5)/2)^2
  have hdef : Constants.phi = (1 + Real.sqrt 5) / 2 := rfl
  have : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2
       = ((1 + Real.sqrt 5) ^ 2) / 4 := by
    ring
  have hsq : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
    have : (1 + Real.sqrt 5) ^ 2 = 1 + 2 * Real.sqrt 5 + (Real.sqrt 5) ^ 2 := by ring
    have : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
      have : 0 ≤ (5 : ℝ) := by norm_num
      simpa [pow_two] using Real.sqrt_mul_self this
    simpa [this] using by
      have : 1 + 2 * Real.sqrt 5 + 5 = 6 + 2 * Real.sqrt 5 := by ring
      simpa [this]
  have hsq_div : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = (6 + 2 * Real.sqrt 5) / 4 := by
    simpa [this] using hsq
  -- Also φ + 1 = ((1+√5)+2)/2
  have hplus : (1 + Real.sqrt 5) / 2 + 1 = (3 + Real.sqrt 5) / 2 := by
    ring
  -- Put everything together
  simpa [hdef, hsq_div, hplus, two_mul, add_comm, add_left_comm, add_assoc] using by
    ring

/-- φ = 1 + 1/φ as a direct algebraic corollary of φ^2 = φ + 1 and φ ≠ 0. -/
@[simp] theorem phi_fixed_point : Constants.phi = 1 + 1 / Constants.phi := by
  have hsq : Constants.phi ^ 2 = Constants.phi + 1 := phi_squared
  have hpos : 0 < Constants.phi := IndisputableMonolith.Constants.phi_pos
  have hne : Constants.phi ≠ 0 := ne_of_gt hpos
  have := congrArg (fun x => x / Constants.phi) hsq
  -- Simplify both sides after dividing by φ
  -- (φ^2)/φ = φ and (φ+1)/φ = 1 + 1/φ
  have : Constants.phi = 1 + 1 / Constants.phi := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
  simpa [add_comm, add_left_comm, add_assoc] using this

end PhiSupport
end IndisputableMonolith
