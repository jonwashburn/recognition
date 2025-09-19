import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace PhiSupport

open Real

/-- φ^2 = φ + 1 using the closed form φ = (1+√5)/2. -/
@[simp] theorem phi_squared : Constants.phi ^ 2 = Constants.phi + 1 := by
  have h : Constants.phi = (1 + Real.sqrt 5) / 2 := rfl
  calc
    Constants.phi ^ 2 = ((1 + Real.sqrt 5) / 2) ^ 2 := by rw [h]
    _ = (1 + 2 * Real.sqrt 5 + 5) / 4 := by ring
    _ = (6 + 2 * Real.sqrt 5) / 4 := by ring
    _ = (3 + Real.sqrt 5) / 2 := by ring
    _ = Constants.phi + 1 := by
      rw [h]
      ring

/-- φ = 1 + 1/φ as a direct algebraic corollary of φ^2 = φ + 1 and φ ≠ 0. -/
@[simp] theorem phi_fixed_point : Constants.phi = 1 + 1 / Constants.phi := by
  have h_sq : Constants.phi ^ 2 = Constants.phi + 1 := phi_squared
  have h_ne_zero : Constants.phi ≠ 0 := Constants.phi_ne_zero
  calc
    Constants.phi = (Constants.phi ^ 2) / Constants.phi := by
      rw [pow_two, mul_div_cancel_left₀ _ h_ne_zero]
    _ = (Constants.phi + 1) / Constants.phi := by rw [h_sq]
    _ = Constants.phi / Constants.phi + 1 / Constants.phi := by rw [add_div]
    _ = 1 + 1 / Constants.phi := by
      have : Constants.phi / Constants.phi = 1 := div_self h_ne_zero
      rw [this]

end PhiSupport
end IndisputableMonolith
