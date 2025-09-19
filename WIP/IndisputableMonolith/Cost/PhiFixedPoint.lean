import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Cost

open Constants

/-- From the constants layer: φ is the positive solution of x = 1 + 1/x. -/
lemma phi_is_cost_fixed_point : phi = 1 + 1 / phi :=
  Constants.phi_fixed_point

end Cost
end IndisputableMonolith


