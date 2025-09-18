import Mathlib
import IndisputableMonolith.Complexity.BalancedParityHidden

namespace IndisputableMonolith
namespace Complexity
namespace LowerBounds

/-- SAT recognition lower bound (dimensionless): any universally-correct fixed-view
    decoder over fewer than n queried indices is impossible. -/
theorem recognition_lower_bound_sat
  (n : ℕ) (M : Finset (Fin n))
  (g : (({i // i ∈ M} → Bool)) → Bool)
  (hMlt : M.card < n) :
  ¬ (∀ (b : Bool) (R : Fin n → Bool),
        g (BalancedParityHidden.restrict (BalancedParityHidden.enc b R) M) = b) := by
  classical
  simpa using (BalancedParityHidden.no_universal_decoder (n:=n) M g)

end LowerBounds
end Complexity
end IndisputableMonolith


