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

/-- Reference identity: w_t(τ0, τ0) = 1. (axiom stub) -/
axiom w_t_ref (P : Params) (τ0 : ℝ) : w_t P τ0 τ0 = 1

lemma w_t_rescale (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t P (c * Tdyn) (c * τ0) = w_t P Tdyn τ0 := by
  dsimp [w_t]
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hc
  have : (c * Tdyn) / (c * τ0) = Tdyn / τ0 := by field_simp [hc0]
  simp [this]

/-- Nonnegativity of time-kernel under ParamProps. (axiom stub) -/
axiom w_t_nonneg (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) : 0 ≤ w_t P Tdyn τ0

end
end ILG
end Gravity
end IndisputableMonolith


