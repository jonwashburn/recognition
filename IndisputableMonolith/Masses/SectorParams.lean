import Mathlib
import IndisputableMonolith

namespace IndisputableMonolith
namespace Masses

/-- Frozen integer parameters per sector: 2^k and φ^r0. -/
structure SectorParams where
  kPow : Nat
  r0   : ℤ

/-- Compute the sector yardstick from params. -/
def yardstickOf (U : Constants.RSUnits) (P : SectorParams) : ℝ :=
  yardstick U P.kPow P.r0

end Masses
end IndisputableMonolith
