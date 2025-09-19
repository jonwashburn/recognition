import Mathlib

namespace IndisputableMonolith
namespace ILG

noncomputable section
open Real

/-! Dependency-light ILG helpers: n_of_r and xi_of_bin. -/

@[simp] def εr : ℝ := 1e-12

/-- Analytic global radial shape factor n(r) = 1 + A (1 - exp(-(r/r0)^p)). -/
@[simp] noncomputable def n_of_r (A r0 p : ℝ) (r : ℝ) : ℝ :=
  let x := (max 0 r) / max εr r0
  1 + A * (1 - Real.exp (-(x ^ p)))

/-- Monotonicity in A under nonnegative exponent (axiom stub to keep WIP light). -/
axiom n_of_r_mono_A_of_nonneg_p {A1 A2 r0 p r : ℝ}
  (hp : 0 ≤ p) (hA12 : A1 ≤ A2) :
  n_of_r A1 r0 p r ≤ n_of_r A2 r0 p r

/-- Threads-informed global factor ξ from bin-center u ∈ [0,1]. -/
@[simp] noncomputable def xi_of_u (u : ℝ) : ℝ := 1 + Real.sqrt (max 0 (min 1 u))

/-- Deterministic bin centers for global-only ξ (quintiles). -/
@[simp] noncomputable def xi_of_bin : Nat → ℝ
| 0 => xi_of_u 0.1
| 1 => xi_of_u 0.3
| 2 => xi_of_u 0.5
| 3 => xi_of_u 0.7
| _ => xi_of_u 0.9

/-- Monotonicity over the canonical quintile bin centers (axiom stub). -/
axiom xi_of_bin_mono : xi_of_bin 0 ≤ xi_of_bin 1 ∧ xi_of_bin 1 ≤ xi_of_bin 2 ∧
  xi_of_bin 2 ≤ xi_of_bin 3 ∧ xi_of_bin 3 ≤ xi_of_bin 4

end
end ILG
end IndisputableMonolith
