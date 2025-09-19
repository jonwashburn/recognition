import Mathlib

namespace IndisputableMonolith
namespace Measurement

/-! WIP: Minimal measurement realization scaffold -/

structure Map (State Obs : Type) where
  T : ℝ
  T_pos : 0 < T
  meas : (ℝ → State) → ℝ → Obs

structure Realization (State Obs : Type) where
  M : Map State Obs
  evolve : Nat → State → State
  invariant8 : Prop
  breath1024 : Prop

end Measurement
end IndisputableMonolith


