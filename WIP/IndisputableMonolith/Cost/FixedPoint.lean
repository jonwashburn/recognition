import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Cost

/-- From the constants layer: φ is the positive solution of x = 1 + 1/x. -/
axiom phi_is_cost_fixed_point : Constants.phi = 1 + 1 / Constants.phi

end Cost
end IndisputableMonolith
