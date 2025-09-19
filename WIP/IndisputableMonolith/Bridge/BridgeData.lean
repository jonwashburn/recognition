import Mathlib
import IndisputableMonolith.Constants -- minimal import; avoids Core cycle

open Real

namespace IndisputableMonolith
namespace Bridge

structure BridgeData where
  G     : ℝ
  hbar  : ℝ
  c     : ℝ
  tau0  : ℝ
  ell0  : ℝ

namespace BridgeData

@[simp] def K_A (_ : BridgeData) : ℝ := Constants.K

/-- Recognition length from anchors: λ_rec = √(ħ G / (π c^3)). -/
@[simp] noncomputable def lambda_rec (B : BridgeData) : ℝ :=
  Real.sqrt (B.hbar * B.G / (Real.pi * (B.c ^ 3)))

structure Physical (B : BridgeData) : Prop where
  c_pos    : 0 < B.c
  hbar_pos : 0 < B.hbar
  G_pos    : 0 < B.G

lemma lambda_rec_pos (B : BridgeData) (H : Physical B) : 0 < lambda_rec B := by
  dsimp [lambda_rec]
  have num_pos : 0 < B.hbar * B.G := mul_pos H.hbar_pos H.G_pos
  have den_pos : 0 < Real.pi * (B.c ^ 3) := by
    have hc3 : 0 < B.c ^ 3 := by simpa using pow_pos H.c_pos (3 : Nat)
    exact mul_pos Real.pi_pos hc3
  have : 0 < (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) := div_pos num_pos den_pos
  exact Real.sqrt_pos.mpr this

@[simp] def K_B (B : BridgeData) : ℝ :=
  lambda_rec B / B.ell0

@[simp] def u_comb (_ : BridgeData) (u_ell0 u_lrec : ℝ) : ℝ := u_ell0 + u_lrec

@[simp] lemma u_comb_comm (B : BridgeData) (a b : ℝ) :
  u_comb B a b = u_comb B b a := by
  simp [u_comb, add_comm]

@[simp] lemma u_comb_zero_right (B : BridgeData) (u : ℝ) : u_comb B u 0 = u := by
  simp [u_comb]

@[simp] lemma u_comb_zero_left (B : BridgeData) (u : ℝ) : u_comb B 0 u = u := by
  simp [u_comb]

@[simp] noncomputable def Zscore (B : BridgeData) (u_ell0 u_lrec k : ℝ) : ℝ :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  (abs (KA - KB)) / (k * u)

@[simp] noncomputable def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  decide ((Zscore B u_ell0 u_lrec k) ≤ 1)

structure Witness where
  KA : ℝ
  KB : ℝ
  u  : ℝ
  Z  : ℝ
  pass : Bool

@[simp] noncomputable def witness (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Witness :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  let Z  := (abs (KA - KB)) / (k * u)
  { KA := KA, KB := KB, u := u, Z := Z, pass := decide (Z ≤ 1) }

@[simp] lemma Zscore_zero_of_KA_eq_KB (B : BridgeData)
  (u_ell0 u_lrec k : ℝ) (h : K_A B = K_B B) :
  Zscore B u_ell0 u_lrec k = 0 := by
  simp [Zscore, h, sub_self]

@[simp] lemma passAt_true_of_KA_eq_KB (B : BridgeData)
  (u_ell0 u_lrec k : ℝ) (h : K_A B = K_B B) :
  passAt B u_ell0 u_lrec k = true := by
  simp [passAt, Zscore_zero_of_KA_eq_KB B u_ell0 u_lrec k h]

end BridgeData

end Bridge

end IndisputableMonolith
