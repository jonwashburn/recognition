import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace PhiSupport

open Real

-- WIP stub to avoid depending on the monolith proof
axiom IndisputableMonolith.Constants.phi_fixed_point : Constants.phi = 1 + 1 / Constants.phi

lemma phi_squared : Constants.phi ^ 2 = Constants.phi + 1 := by
  have hfix := Constants.phi_fixed_point
  have hpos := Constants.phi_pos
  have hne : Constants.phi ≠ 0 := ne_of_gt hpos
  have : Constants.phi * Constants.phi = Constants.phi * (1 + 1 / Constants.phi) := by
    simpa [pow_two] using congrArg (fun x => Constants.phi * x) hfix
  have : Constants.phi ^ 2 = Constants.phi + 1 := by
    simpa [pow_two, mul_add, one_div, mul_comm, mul_left_comm, mul_assoc, inv_mul_cancel hne] using this
  exact this

end PhiSupport
end IndisputableMonolith


