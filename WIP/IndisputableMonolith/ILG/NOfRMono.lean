import Mathlib
import IndisputableMonolith.ILG.ParamsKernel

namespace IndisputableMonolith
namespace ILG

noncomputable section
open Real

/-- Monotonicity in A under nonnegative exponent: if p ≥ 0 and A₁ ≤ A₂ then
    n_of_r A₁ ≤ n_of_r A₂ (for fixed r0,p,r). -/
theorem n_of_r_mono_A_of_nonneg_p {A1 A2 r0 p r : ℝ}
  (hp : 0 ≤ p) (hA12 : A1 ≤ A2) :
  n_of_r A1 r0 p r ≤ n_of_r A2 r0 p r := by
  dsimp [n_of_r]
  -- Let t := ((max 0 r) / max εr r0)^p ≥ 0 when p ≥ 0 and base ≥ 0
  set t := ((max 0 r) / max εr r0) ^ p with ht
  have hden_pos : 0 < max εr r0 := by
    have : 0 < εr := by norm_num [εr]
    exact lt_of_le_of_lt (le_max_left _ _) this
  have hbase_nonneg : 0 ≤ (max 0 r) / max εr r0 := by
    have : 0 ≤ max 0 r := le_max_left _ _
    exact div_nonneg this (le_of_lt hden_pos)
  have ht_nonneg : 0 ≤ t := by
    have := Real.rpow_nonneg_of_nonneg hbase_nonneg p
    simpa [ht] using this
  -- exp(−t) ≤ 1 when t ≥ 0 ⇒ (1 − exp(−t)) ≥ 0
  have hterm_nonneg : 0 ≤ 1 - Real.exp (-t) := by
    exact sub_nonneg.mpr ((Real.exp_neg_le_one_iff).mpr ht_nonneg)
  -- Multiply the nonnegative term by A preserves ≤ when A grows
  have : A1 * (1 - Real.exp (-t)) ≤ A2 * (1 - Real.exp (-t)) :=
    mul_le_mul_of_nonneg_right hA12 hterm_nonneg
  simpa [ht, add_comm, add_left_comm, add_assoc]
    using add_le_add_left this 1

end
end ILG
end IndisputableMonolith


