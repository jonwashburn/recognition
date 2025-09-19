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

end PhiSupport
end IndisputableMonolith
