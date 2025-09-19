import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Bridge
namespace BridgeData

/-- External bridge anchors provided as data (no axioms): G, ħ, c, plus display anchors. -/
structure BridgeData where
  G     : ℝ
  hbar  : ℝ
  c     : ℝ
  tau0  : ℝ
  ell0  : ℝ
  deriving Repr

namespace BridgeData

@[simp] def K_A (_ : BridgeData) : ℝ := Constants.K

/-- Recognition length from anchors: λ_rec = √(ħ G / c^3). -/
@[simp] def lambda_rec (B : BridgeData) : ℝ :=
  Real.sqrt (B.hbar * B.G / (Real.pi * (B.c ^ 3)))

/-- Minimal physical assumptions on bridge anchors reused by analytical lemmas. -/
structure Physical (B : BridgeData) : Prop where
  c_pos    : 0 < B.c
  hbar_pos : 0 < B.hbar
  G_pos    : 0 < B.G

/-- Dimensionless identity for λ_rec (under mild physical positivity assumptions):
    (c^3 · λ_rec^2) / (ħ G) = 1/π. -/
lemma lambda_rec_dimensionless_id (B : BridgeData)
  (hc : 0 < B.c) (hh : 0 < B.hbar) (hG : 0 < B.G) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hc3_pos : 0 < B.c ^ 3 := by
    have := pow_pos hc (3 : Nat)
    simpa using this
  have hden_pos : 0 < Real.pi * (B.c ^ 3) := mul_pos hpi_pos hc3_pos
  have hnum_nonneg : 0 ≤ B.hbar * B.G := mul_nonneg (le_of_lt hh) (le_of_lt hG)
  have hrad_nonneg : 0 ≤ (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  -- Square of sqrt is the radicand
  have hsq : (lambda_rec B) ^ 2
      = (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) := by
    dsimp [lambda_rec]
    have := Real.mul_self_sqrt hrad_nonneg
    simpa [pow_two] using this
  -- Compute the dimensionless ratio
  have hprod_ne : B.hbar * B.G ≠ 0 := mul_ne_zero (ne_of_gt hh) (ne_of_gt hG)
  have hc3_ne : B.c ^ 3 ≠ 0 := ne_of_gt hc3_pos
  calc
    (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G)
        = (B.c ^ 3) * (((B.hbar * B.G) / (Real.pi * (B.c ^ 3))) / (B.hbar * B.G)) := by simpa [hsq]
    _   = (B.c ^ 3) * ((B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G))) := by
          -- a*b/c = a*(b/c); (x/y)/z = x/(y*z)
          have : ((B.hbar * B.G) / (Real.pi * (B.c ^ 3))) / (B.hbar * B.G)
                    = (B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G)) := by
            simpa [div_div, mul_comm, mul_left_comm, mul_assoc]
          -- reorder factors to isolate 1/(π c^3)
          calc
            (B.c ^ 3) * (((B.hbar * B.G) / (Real.pi * (B.c ^ 3))) / (B.hbar * B.G))
                = (B.c ^ 3) * ((B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G))) := by simpa [this]
            _ = ((B.c ^ 3) / (Real.pi * (B.c ^ 3))) * ((B.hbar * B.G) / (B.hbar * B.G)) := by
                field_simp
    _   = ((B.c ^ 3) / (Real.pi * (B.c ^ 3))) * 1 := by simp [hprod_ne]
    _   = 1 / Real.pi := by
          have : (B.c ^ 3) / (B.c ^ 3) = (1 : ℝ) := by simpa [div_self hc3_ne]
          -- (a)/(π a) = (1/π) * (a/a)
          have := by
            have : (B.c ^ 3) / (Real.pi * (B.c ^ 3)) = (1 / Real.pi) * ((B.c ^ 3) / (B.c ^ 3)) := by
              field_simp
            simpa [this]
          -- simplify to 1/π
          simpa [this]

/-- Dimensionless identity packaged with a physical-assumptions helper. -/
lemma lambda_rec_dimensionless_id_physical (B : BridgeData) (H : Physical B) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi :=
  lambda_rec_dimensionless_id B H.c_pos H.hbar_pos H.G_pos

/-- Positivity of λ_rec under physical assumptions. -/
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

/-- Combined uncertainty aggregator (placeholder policy). -/
@[simp] def u_comb (_ : BridgeData) (u_ell0 u_lrec : ℝ) : ℝ := u_ell0 + u_lrec

/-- Symbolic K-gate Z-score witness: Z = |K_A − K_B| / (k·u_comb). -/
@[simp] def Zscore (B : BridgeData) (u_ell0 u_lrec k : ℝ) : ℝ :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  (Real.abs (KA - KB)) / (k * u)

/-- Boolean pass at threshold k: Z ≤ 1. Publishes the exact Z expression. -/
@[simp] def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  decide ((Zscore B u_ell0 u_lrec k) ≤ 1)

/-- Full witness record for publication. -/
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

/-- Tick from anchors via hop map λ_rec = c · τ0. -/
@[simp] def tau0 (B : BridgeData) : ℝ := lambda_rec B / B.c

/-- Coherence energy: E_coh = φ^-5 · (2π ħ / τ0). -/
@[simp] def E_coh (B : BridgeData) : ℝ :=
  Constants.PhiPow (-5) * (2 * Real.pi * B.hbar / tau0 B)

/-- Dimensionless inverse fine-structure constant (seed–gap–curvature). -/
@[simp] def alphaInv : ℝ :=
  4 * Real.pi * 11 - (Real.log Constants.phi + (103 : ℝ) / (102 * Real.pi ^ 5))

/-- Fine-structure constant α. -/
@[simp] def alpha : ℝ := 1 / alphaInv

/-- Stub for electron mass ratio (depends on Recognition) -/
axiom m_e_over_Ecoh : ℝ

/-- Electron mass: m_e = (m_e/E_coh) · E_coh. -/
@[simp] def m_e (B : BridgeData) : ℝ := m_e_over_Ecoh * E_coh B

/-- Bohr radius a0 = ħ / (m_e c α). -/
@[simp] def a0_bohr (B : BridgeData) : ℝ :=
  B.hbar / (m_e B * B.c * alpha)

end BridgeData
end Bridge
end IndisputableMonolith