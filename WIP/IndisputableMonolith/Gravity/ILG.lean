import Mathlib

namespace IndisputableMonolith
namespace Gravity
namespace ILG

noncomputable section
open Real

/-! Local WIP stubs to avoid internal imports. -/
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

/-- Reference identity: w_t(τ0, τ0) = 1. -/
lemma w_t_ref (P : Params) (τ0 : ℝ) : w_t P τ0 τ0 = 1 := by
  dsimp [w_t]
  have : max εt ((τ0 : ℝ) / τ0) = 1 := by
    by_cases hτ : τ0 = 0
    · simp [hτ]
    · have : (τ0 : ℝ) / τ0 = (1 : ℝ) := by field_simp [hτ]
      have hε : εt ≤ (1 : ℝ) := by norm_num
      simpa [this, max_eq_right hε]
  simp [this, Real.rpow_one]

/-- Rescaling invariance: (c⋅Tdyn, c⋅τ0) leaves w_t unchanged for c>0. -/
lemma w_t_rescale (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t P (c * Tdyn) (c * τ0) = w_t P Tdyn τ0 := by
  dsimp [w_t]
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hc
  have : (c * Tdyn) / (c * τ0) = Tdyn / τ0 := by field_simp [hc0]
  simp [this]

/-- Nonnegativity of time-kernel under ParamProps. -/
lemma w_t_nonneg (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) : 0 ≤ w_t P Tdyn τ0 := by
  dsimp [w_t]
  have hpow_nonneg : 0 ≤ Real.rpow (max εt (Tdyn / τ0)) P.alpha :=
    Real.rpow_nonneg_of_nonneg (le_max_left _ _) _
  have hge : 1 - P.Clag ≤ 1 + P.Clag * (Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1) := by
    have hdiff : 0 ≤ Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1 := sub_nonneg.mpr (by simpa using hpow_nonneg)
    have : 0 ≤ P.Clag * (Real.rpow (max εt (Tdyn / τ0)) P.alpha - 1) := mul_nonneg H.Clag_nonneg hdiff
    simpa [sub_eq, add_comm, add_left_comm, add_assoc] using add_le_add_left this 1
  exact (sub_nonneg.mpr H.Clag_le_one).trans hge

end
end ILG
end Gravity
end IndisputableMonolith


