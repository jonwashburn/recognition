import Mathlib
import IndisputableMonolith.Constants -- use Constants.K without creating a cycle

namespace IndisputableMonolith
namespace Bridge

structure BridgeData where
  G     : ℝ
  hbar  : ℝ
  c     : ℝ
  tau0  : ℝ
  ell0  : ℝ
  deriving Repr

namespace BridgeData

@[simp] def K_A (_ : BridgeData) : ℝ := Constants.K

/-- Recognition length from anchors: λ_rec = √(ħ G / (π c^3)). -/
@[simp] def lambda_rec (B : BridgeData) : ℝ :=
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

lemma lambda_rec_dimensionless_id (B : BridgeData)
  (hc : 0 < B.c) (hh : 0 < B.hbar) (hG : 0 < B.G) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hc3_pos : 0 < B.c ^ 3 := by simpa using pow_pos hc (3 : Nat)
  have hden_pos : 0 < Real.pi * (B.c ^ 3) := mul_pos hpi_pos hc3_pos
  have hnum_nonneg : 0 ≤ B.hbar * B.G := mul_nonneg (le_of_lt hh) (le_of_lt hG)
  have hrad_nonneg : 0 ≤ (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hsq : (lambda_rec B) ^ 2
      = (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) := by
    dsimp [lambda_rec]
    have := Real.mul_self_sqrt hrad_nonneg
    simpa [pow_two] using this
  have hprod_ne : B.hbar * B.G ≠ 0 := mul_ne_zero (ne_of_gt hh) (ne_of_gt hG)
  have hc3_ne : B.c ^ 3 ≠ 0 := ne_of_gt hc3_pos
  calc
    (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G)
        = (B.c ^ 3) * (((B.hbar * B.G) / (Real.pi * (B.c ^ 3))) ) / (B.hbar * B.G) := by
              simpa [hsq]
    _   = (((B.c ^ 3) * (B.hbar * B.G)) / (Real.pi * (B.c ^ 3))) / (B.hbar * B.G) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (mul_div_assoc (B.c ^ 3) (B.hbar * B.G) (Real.pi * (B.c ^ 3))).symm
    _   = ((B.c ^ 3) * (B.hbar * B.G)) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G)) := by
              simpa using (div_div_eq_mul_div ((B.c ^ 3) * (B.hbar * B.G)) (Real.pi * (B.c ^ 3)) (B.hbar * B.G))
    _   = (B.c ^ 3) / (Real.pi * (B.c ^ 3)) := by
              simpa using (mul_div_mul_right ((B.c ^ 3)) (Real.pi * (B.c ^ 3)) (B.hbar * B.G))
    _   = 1 / Real.pi := by
              have : (B.c ^ 3) / (Real.pi * (B.c ^ 3)) = (B.c ^ 3) / ((B.c ^ 3) * Real.pi) := by
                simpa [mul_comm]
              have : (B.c ^ 3) / ((B.c ^ 3) * Real.pi) = ((B.c ^ 3) / (B.c ^ 3)) / Real.pi := by
                simpa [div_mul_eq_mul_div]
              have : ((B.c ^ 3) / (B.c ^ 3)) / Real.pi = 1 / Real.pi := by
                have hself : (B.c ^ 3) / (B.c ^ 3) = (1 : ℝ) := by simpa [hc3_ne] using (div_self hc3_ne)
                simpa [hself]
              simpa using this

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

@[simp] lemma u_comb_add_left (B : BridgeData) (a b c : ℝ) :
  u_comb B (a + b) c = a + b + c := by
  simp [u_comb, add_assoc]

@[simp] lemma u_comb_add_right (B : BridgeData) (a b c : ℝ) :
  u_comb B a (b + c) = a + (b + c) := by
  simp [u_comb, add_assoc]

@[simp] lemma u_comb_assoc (B : BridgeData) (a b c : ℝ) :
  u_comb B (u_comb B a b) c = u_comb B a (u_comb B b c) := by
  simp [u_comb, add_assoc]

@[simp] def Zscore (B : BridgeData) (u_ell0 u_lrec k : ℝ) : ℝ :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  (Real.abs (KA - KB)) / (k * u)

@[simp] def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  decide ((Zscore B u_ell0 u_lrec k) ≤ 1)

structure Witness where
  KA : ℝ
  KB : ℝ
  u  : ℝ
  Z  : ℝ
  pass : Bool
  deriving Repr

@[simp] def witness (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Witness :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  let Z  := (Real.abs (KA - KB)) / (k * u)
  { KA := KA, KB := KB, u := u, Z := Z, pass := decide (Z ≤ 1) }

/-- Tick from anchors via hop map `λ_rec = c · τ0`. -/
@[simp] def tau0 (B : BridgeData) : ℝ := lambda_rec B / B.c

/-- Coherence energy: `E_coh = φ^-5 · (2π ħ / τ0)`. -/
@[simp] def E_coh (B : BridgeData) : ℝ :=
  (1 / (IndisputableMonolith.Constants.phi ^ (5 : Nat))) * (2 * Real.pi * B.hbar / (tau0 B))

/-- Dimensionless inverse fine-structure constant (seed–gap–curvature). -/
@[simp] def alphaInv : ℝ :=
  4 * Real.pi * 11 - (Real.log IndisputableMonolith.Constants.phi + (103 : ℝ) / (102 * Real.pi ^ 5))

/-- Fine-structure constant α. -/
@[simp] def alpha : ℝ := 1 / alphaInv

/-! ### Electron mass wrapper (dimensionless ratio times coherence energy) -/

/-- Dimensionless electron mass ratio `m_e / E_coh` (placeholder constant). -/
@[simp] def m_e_over_Ecoh : ℝ := 1

/-- Electron mass: `m_e = (m_e / E_coh) · E_coh`. -/
@[simp] def m_e (B : BridgeData) : ℝ := m_e_over_Ecoh * E_coh B

@[simp] lemma Zscore_zero_of_KA_eq_KB (B : BridgeData)
  (u_ell0 u_lrec k : ℝ) (h : K_A B = K_B B) :
  Zscore B u_ell0 u_lrec k = 0 := by
  simp [Zscore, h, sub_self]

@[simp] lemma passAt_true_of_KA_eq_KB (B : BridgeData)
  (u_ell0 u_lrec k : ℝ) (h : K_A B = K_B B) :
  passAt B u_ell0 u_lrec k = true := by
  simp [passAt, Zscore_zero_of_KA_eq_KB B u_ell0 u_lrec k h]

lemma Zscore_nonneg
  (B : BridgeData) (u_ell0 u_lrec k : ℝ)
  (hk : 0 < k) (hu : 0 < u_comb B u_ell0 u_lrec) :
  0 ≤ Zscore B u_ell0 u_lrec k := by
  unfold Zscore
  have hden_pos : 0 < k * (u_comb B u_ell0 u_lrec) := mul_pos hk hu
  have hnum_nonneg : 0 ≤ Real.abs (K_A B - K_B B) := by exact abs_nonneg _
  exact div_nonneg hnum_nonneg (le_of_lt hden_pos)

lemma u_comb_nonneg (B : BridgeData) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
  0 ≤ u_comb B a b := by
  simp [u_comb, add_nonneg, ha, hb]

lemma passAt_false_of_gt (B : BridgeData) (u_ell0 u_lrec k : ℝ)
  (h : 1 < Zscore B u_ell0 u_lrec k) :
  passAt B u_ell0 u_lrec k = false := by
  simp [passAt, not_le.mpr h]

end BridgeData

end Bridge

end IndisputableMonolith
