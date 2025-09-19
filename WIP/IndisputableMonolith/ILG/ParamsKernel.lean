import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace ILG

def εr : ℝ := 1e-12
def εt : ℝ := 1e-12

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

def n_of_r (A r0 p : ℝ) (r : ℝ) : ℝ :=
  let x := (max 0 r) / max εr r0
  1 + A * (1 - Real.exp (-(x ^ p)))

@[simp] def n_profile (P : Params) (r : ℝ) : ℝ := n_of_r P.A P.r0 P.p r
@[simp] def zeta (P : Params) (r : ℝ) : ℝ := r  -- lightweight placeholder; original used zeta_of_r
@[simp] def xi (P : Params) (u : ℝ) : ℝ := 1 + P.Clag * Real.sqrt (max 0 (min 1 u))

@[simp] def w_t (P : Params) (Tdyn τ0 : ℝ) : ℝ :=
  let t := max εt (Tdyn / τ0)
  1 + P.Clag * (Real.rpow t P.alpha - 1)

@[simp] def w_t_display (P : Params) (_B : Unit) (Tdyn : ℝ) : ℝ :=
  w_t P Tdyn 1

lemma w_t_ref (P : Params) (τ0 : ℝ) : w_t P τ0 τ0 = 1 := by
  dsimp [w_t]
  have : max εt ((τ0 : ℝ) / τ0) = 1 := by
    by_cases hτ : τ0 = 0
    · simp [hτ]
    · have : (τ0 : ℝ) / τ0 = (1 : ℝ) := by field_simp [hτ]
      have hε : εt ≤ (1 : ℝ) := by norm_num
      simpa [this, max_eq_right hε]
  simp [this, Real.rpow_one]

lemma w_t_rescale (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t P (c * Tdyn) (c * τ0) = w_t P Tdyn τ0 := by
  dsimp [w_t]
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hc
  have : (c * Tdyn) / (c * τ0) = Tdyn / τ0 := by field_simp [hc0]
  simp [this]

lemma w_t_nonneg (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) : 0 ≤ w_t P Tdyn τ0 := by
  dsimp [w_t]
  have hpow_nonneg : 0 ≤ Real.rpow (max εt (Tdyn / τ0)) P.alpha :=
    Real.rpow_nonneg_of_nonneg (le_max_left _ _) _
  have hge : 1 - P.Clag ≤ 1 + P.Clag * (Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1) := by
    have hdiff : 0 ≤ Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1 := sub_nonneg.mpr (by simpa using hpow_nonneg)
    have : 0 ≤ P.Clag * (Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1) := mul_nonneg H.Clag_nonneg hdiff
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using add_le_add_left this 1
  exact (sub_nonneg.mpr H.Clag_le_one).trans hge

lemma n_of_r_mono_A_of_nonneg_p {A1 A2 r0 p r : ℝ}
  (hp : 0 ≤ p) (hA12 : A1 ≤ A2) :
  n_of_r A1 r0 p r ≤ n_of_r A2 r0 p r := by
  dsimp [n_of_r]
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
  have hterm_nonneg : 0 ≤ 1 - Real.exp (-t) := by
    exact sub_nonneg.mpr ((Real.exp_neg_le_one_iff).mpr ht_nonneg)
  have : A1 * (1 - Real.exp (-t)) ≤ A2 * (1 - Real.exp (-t)) :=
    mul_le_mul_of_nonneg_right hA12 hterm_nonneg
  simpa [ht, add_comm, add_left_comm, add_assoc] using add_le_add_left this 1

def xi_of_u (u : ℝ) : ℝ := 1 + Constants.Clag * Real.sqrt (max 0 (min 1 u))

def xi_of_bin : Nat → ℝ
| 0 => xi_of_u 0.1
| 1 => xi_of_u 0.3
| 2 => xi_of_u 0.5
| 3 => xi_of_u 0.7
| _ => xi_of_u 0.9

end ILG
end IndisputableMonolith


