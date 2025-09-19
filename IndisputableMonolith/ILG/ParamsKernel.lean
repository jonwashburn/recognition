import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace ILG

noncomputable def εr : ℝ := 1e-12
noncomputable def εt : ℝ := 1e-12

structure Params where
  alpha      : ℝ
  Clag       : ℝ
  A          : ℝ
  r0         : ℝ
  p          : ℝ
  hz_over_Rd : ℝ

structure ParamProps (P : Params) : Prop where
  alpha_nonneg : 0 ≤ P.alpha
  Clag_nonneg  : 0 ≤ P.Clag
  Clag_le_one  : P.Clag ≤ 1
  A_nonneg     : 0 ≤ P.A
  r0_pos       : 0 < P.r0
  p_pos        : 0 < P.p

noncomputable def n_of_r (A r0 p : ℝ) (r : ℝ) : ℝ :=
  let x := (max 0 r) / max εr r0
  1 + A * (1 - Real.exp (-(x ^ p)))

@[simp] noncomputable def n_profile (P : Params) (r : ℝ) : ℝ := n_of_r P.A P.r0 P.p r
@[simp] noncomputable def zeta (P : Params) (r : ℝ) : ℝ := r  -- lightweight placeholder; original used zeta_of_r
@[simp] noncomputable def xi (P : Params) (u : ℝ) : ℝ := 1 + P.Clag * Real.sqrt (max 0 (min 1 u))

@[simp] noncomputable def w_t (P : Params) (Tdyn τ0 : ℝ) : ℝ :=
  let t := max εt (Tdyn / τ0)
  1 + P.Clag * (Real.rpow t P.alpha - 1)

@[simp] noncomputable def w_t_display (P : Params) (_B : Unit) (Tdyn : ℝ) : ℝ :=
  w_t P Tdyn 1

lemma w_t_ref (P : Params) (τ0 : ℝ) : w_t P τ0 τ0 = 1 := by
  -- w_t P τ0 τ0 = 1 + P.Clag * (1^P.alpha - 1) = 1 + P.Clag * 0 = 1
  simp [w_t]
  ring

lemma w_t_rescale (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t P (c * Tdyn) (c * τ0) = w_t P Tdyn τ0 := by
  -- w_t scales as (Tdyn/τ0)^alpha, so (c*Tdyn)/(c*τ0) = Tdyn/τ0
  simp [w_t]
  congr 2
  rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div]
  simp [mul_div_cancel_left₀ _ (ne_of_gt hc)]

lemma w_t_nonneg (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) : 0 ≤ w_t P Tdyn τ0 := by
  -- w_t = 1 + P.Clag * (t^α - 1) where t ≥ εt > 0
  -- Since P.Clag ≥ 0 and t^α ≥ εt^α > 0, we need to show this is ≥ 0
  simp [w_t]
  have h_t_pos : 0 < max εt (Tdyn / τ0) := by
    apply lt_max_of_lt_left
    simp [εt]
    norm_num
  have h_rpow_pos : 0 < Real.rpow (max εt (Tdyn / τ0)) P.alpha := by
    exact Real.rpow_pos_of_pos h_t_pos P.alpha
  -- The key insight: for any t > 0 and α ≥ 0, we have 1 + Clag*(t^α - 1) ≥ 1 - Clag ≥ 0
  have h_bound : Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1 ≥ -1 := by
    -- t^α ≥ 0 implies t^α - 1 ≥ -1
    have : 0 ≤ Real.rpow (max εt (Tdyn / τ0)) P.alpha := le_of_lt h_rpow_pos
    linarith
  have : P.Clag * (Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1) ≥ P.Clag * (-1) := by
    exact mul_le_mul_of_nonneg_left h_bound H.Clag_nonneg
  have : P.Clag * (Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1) ≥ -P.Clag := by
    simpa [mul_neg, mul_one] using this
  have : 1 + P.Clag * (Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1) ≥ 1 - P.Clag := by
    linarith
  -- Since P.Clag ≤ 1, we have 1 - P.Clag ≥ 0
  have : 0 ≤ 1 - P.Clag := by linarith [H.Clag_le_one]
  linarith

theorem n_of_r_mono_A_of_nonneg_p {A1 A2 r0 p r : ℝ}
  (hp : 0 ≤ p) (hA12 : A1 ≤ A2) :
  n_of_r A1 r0 p r ≤ n_of_r A2 r0 p r := by
  -- reuse the monolith proof pattern specialized here
  dsimp [n_of_r]
  set t := ((max 0 r) / max εr r0) ^ p with ht
  have hden_pos : 0 < max εr r0 := by
    have : 0 < εr := by
      -- small positive guard
      have : (1e-12 : ℝ) > 0 := by norm_num
      simpa [εr] using this
    exact lt_max_of_lt_left this
  have hbase_nonneg : 0 ≤ (max 0 r) / max εr r0 := by
    have : 0 ≤ max 0 r := le_max_left _ _
    exact div_nonneg this (le_of_lt hden_pos)
  have ht_nonneg : 0 ≤ t := by
    -- for p ≥ 0, (positive)^p ≥ 0
    have : 0 ≤ (max 0 r) / max εr r0 := hbase_nonneg
    exact Real.rpow_nonneg this hp
  have hterm_nonneg : 0 ≤ 1 - Real.exp (-t) := by
    have : Real.exp (-t) ≤ 1 := by
      -- exp(x) ≤ 1 for x ≤ 0
      have : -t ≤ 0 := neg_nonpos.mpr ht_nonneg
      -- for x ≤ 0, exp(x) ≤ 1
      exact Real.exp_le_one_of_nonpos this
    exact sub_nonneg.mpr this
  have : A1 * (1 - Real.exp (-t)) ≤ A2 * (1 - Real.exp (-t)) :=
    mul_le_mul_of_nonneg_right hA12 hterm_nonneg
  simpa [ht, add_comm, add_left_comm, add_assoc]
    using add_le_add_left this 1

noncomputable def xi_of_u (u : ℝ) : ℝ := 1 + Real.sqrt (max 0 (min 1 u))

noncomputable def xi_of_bin : Nat → ℝ
| 0 => xi_of_u 0.1
| 1 => xi_of_u 0.3
| 2 => xi_of_u 0.5
| 3 => xi_of_u 0.7
| _ => xi_of_u 0.9

end ILG
end IndisputableMonolith
