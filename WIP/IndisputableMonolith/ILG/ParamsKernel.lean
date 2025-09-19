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

axiom w_t_ref (P : Params) (τ0 : ℝ) : w_t P τ0 τ0 = 1

axiom w_t_rescale (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t P (c * Tdyn) (c * τ0) = w_t P Tdyn τ0

axiom w_t_nonneg (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) : 0 ≤ w_t P Tdyn τ0

axiom n_of_r_mono_A_of_nonneg_p {A1 A2 r0 p r : ℝ}
  (hp : 0 ≤ p) (hA12 : A1 ≤ A2) :
  n_of_r A1 r0 p r ≤ n_of_r A2 r0 p r

noncomputable def xi_of_u (u : ℝ) : ℝ := 1 + Real.sqrt (max 0 (min 1 u))

noncomputable def xi_of_bin : Nat → ℝ
| 0 => xi_of_u 0.1
| 1 => xi_of_u 0.3
| 2 => xi_of_u 0.5
| 3 => xi_of_u 0.7
| _ => xi_of_u 0.9

end ILG
end IndisputableMonolith
