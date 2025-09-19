import Mathlib
import IndisputableMonolith.Bridge.BridgeData

namespace IndisputableMonolith
namespace Gravity
namespace ILG

noncomputable section
open Real

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

@[simp] def w_t_display (P : Params) (B : Bridge.BridgeData) (Tdyn : ℝ) : ℝ :=
  w_t P Tdyn B.tau0

end
end ILG
end Gravity
end IndisputableMonolith


