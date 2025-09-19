import Mathlib

namespace IndisputableMonolith
namespace Gravity
namespace ILG

noncomputable section
open Real

/-! Minimal extracted time-kernel basics (axiom stubs). -/

structure BridgeData where
  tau0 : ℝ

structure BaryonCurves where
  vgas  : ℝ → ℝ
  vdisk : ℝ → ℝ
  vbul  : ℝ → ℝ

def upsilonStar : ℝ := 1.0
def εr : ℝ := 1e-12
def εv : ℝ := 1e-12
def εt : ℝ := 1e-12
def εa : ℝ := 1e-12

def vbarSq (C : BaryonCurves) (r : ℝ) : ℝ :=
  max 0 ((C.vgas r) ^ 2 + ((Real.sqrt upsilonStar) * (C.vdisk r)) ^ 2 + (C.vbul r) ^ 2)

def vbar (C : BaryonCurves) (r : ℝ) : ℝ :=
  Real.sqrt (max εv (vbarSq C r))

def gbar (C : BaryonCurves) (r : ℝ) : ℝ :=
  (vbar C r) ^ 2 / max εr r

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

def w_t (P : Params) (Tdyn τ0 : ℝ) : ℝ :=
  let t := max εt (Tdyn / τ0)
  1 + P.Clag * (Real.rpow t P.alpha - 1)

@[simp] def w_t_display (P : Params) (B : BridgeData) (Tdyn : ℝ) : ℝ :=
  w_t P Tdyn B.tau0

/-– Auxiliary: εt ≤ 1 for the chosen numerical constant. -/
lemma eps_t_le_one : εt ≤ (1 : ℝ) := by
  -- 1e-12 ≤ 1
  norm_num [εt]

/-- Reference identity under nonzero tick: w_t(τ0, τ0) = 1. -/
lemma w_t_ref (P : Params) (τ0 : ℝ) (hτ : τ0 ≠ 0) : w_t P τ0 τ0 = 1 := by
  dsimp [w_t]
  have hdiv : τ0 / τ0 = (1 : ℝ) := by
    field_simp [hτ]
  have hmax : max εt (τ0 / τ0) = (1 : ℝ) := by
    simpa [hdiv, max_eq_right eps_t_le_one]
  simp [hmax]

lemma w_t_rescale (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t P (c * Tdyn) (c * τ0) = w_t P Tdyn τ0 := by
  dsimp [w_t]
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hc
  have : (c * Tdyn) / (c * τ0) = Tdyn / τ0 := by field_simp [hc0]
  simp [this]

/-- Nonnegativity of time-kernel under ParamProps. -/
lemma w_t_nonneg (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) : 0 ≤ w_t P Tdyn τ0 := by
  dsimp [w_t]
  set t := max εt (Tdyn / τ0) with ht
  have ht_nonneg : 0 ≤ t := by
    have hε : 0 ≤ εt := by norm_num [εt]
    have : εt ≤ t := by
      simpa [ht] using le_max_left εt (Tdyn / τ0)
    exact le_trans hε this
  have hrpow_nonneg : 0 ≤ Real.rpow t P.alpha := Real.rpow_nonneg_of_nonneg ht_nonneg _
  -- Bound: Real.rpow t α − 1 ≥ −1
  have hge : Real.rpow t P.alpha - 1 ≥ -1 := by
    have : (0 : ℝ) ≤ Real.rpow t P.alpha := hrpow_nonneg
    have : -1 ≤ Real.rpow t P.alpha - 1 := by linarith
    simpa [sub_eq_add_neg] using this
  -- Scale by 0 ≤ Clag ≤ 1
  have hClag_nonneg : 0 ≤ P.Clag := H.Clag_nonneg
  have hClag_le_one : P.Clag ≤ 1 := H.Clag_le_one
  have hscale : P.Clag * (Real.rpow t P.alpha - 1) ≥ -1 := by
    -- Since (Real.rpow t α − 1) ≥ −1 and 0 ≤ Clag ≤ 1, we have Clag * (⋯) ≥ −1
    have : -1 ≤ Real.rpow t P.alpha - 1 := by
      have : (0 : ℝ) ≤ Real.rpow t P.alpha := hrpow_nonneg
      linarith
    -- Multiply inequality by nonnegative Clag preserves direction
    have := mul_le_mul_of_nonneg_left this hClag_nonneg
    -- Clag * (-1) ≥ -1 since Clag ≤ 1
    have hleft : (-1 : ℝ) ≤ P.Clag * (-1) := by
      have : -1 ≤ -P.Clag := by simpa using (neg_le_neg hClag_le_one)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    -- Combine lower bounds: Clag*(rpow−1) ≥ Clag*(-1) and ≥ -1; pick the weaker bound -1
    have : P.Clag * (Real.rpow t P.alpha - 1) ≥ P.Clag * (-1) := by
      -- from mul_le_mul result above
      have h := this
      simpa [sub_eq_add_neg] using h
    exact le_trans hleft this
  -- Now 1 + Clag*(⋯) ≥ 0
  have : 0 ≤ 1 + P.Clag * (Real.rpow t P.alpha - 1) := by
    have : -1 ≤ P.Clag * (Real.rpow t P.alpha - 1) := by
      -- from hscale, rewrite ≥ as ≤ after multiplying by -1
      simpa [neg_le] using hscale
    linarith
  simpa [w_t, ht, add_comm, add_left_comm, add_assoc] using this

end
end ILG
end Gravity
end IndisputableMonolith
