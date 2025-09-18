import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace RH
namespace RS

/-! Binary scales and φ-exponential wrappers -/

/-- Binary scale factor `B = 2^k` as a real. -/
def B_of (k : Nat) : ℝ := (2 : ℝ) ^ k

@[simp] lemma B_of_zero : B_of 0 = 1 := by simp [B_of]

@[simp] lemma B_of_succ (k : Nat) : B_of (k+1) = 2 * B_of k := by
  simp [B_of, pow_succ, mul_comm]

lemma B_of_pos (k : Nat) : 0 < B_of k := by
  have : 0 < (2:ℝ) := by norm_num
  simpa [B_of] using pow_pos this k

@[simp] lemma B_of_nonneg (k : Nat) : 0 ≤ B_of k := by
  exact le_of_lt (B_of_pos k)

@[simp] lemma B_of_one : B_of 1 = 2 := by simp [B_of]

lemma one_le_B_of (k : Nat) : (1 : ℝ) ≤ B_of k := by
  induction k with
  | zero => simp [B_of]
  | succ k ih =>
      have hmul : (2 : ℝ) ≤ 2 * B_of k := by
        have : 2 * (1 : ℝ) ≤ 2 * B_of k := by
          have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
          exact mul_le_mul_of_nonneg_left ih hnonneg
        simpa using this
      have h12 : (1 : ℝ) ≤ 2 := by norm_num
      have : (1 : ℝ) ≤ 2 * B_of k := le_trans h12 hmul
      simpa [B_of_succ, mul_comm] using this

lemma B_of_add (a b : Nat) : B_of (a + b) = B_of a * B_of b := by
  simp [B_of, pow_add, mul_comm, mul_left_comm, mul_assoc]

lemma B_of_le_add_left (k m : Nat) : B_of k ≤ B_of (k + m) := by
  have hk : k ≤ k + m := Nat.le_add_right _ _
  exact B_of_le_of_le hk

lemma B_of_le_of_le {k n : Nat} (hkn : k ≤ n) : B_of k ≤ B_of n := by
  -- write n = k + m
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  -- B_of (k+m) = B_of k * B_of m
  have : B_of (k + m) = B_of k * B_of m := by
    simp [B_of, pow_add, mul_comm, mul_left_comm, mul_assoc]
  -- 1 ≤ B_of m
  have h1 : (1 : ℝ) ≤ B_of m := one_le_B_of m
  -- nonneg of left factor
  have hnonneg : 0 ≤ B_of k := by simpa using B_of_nonneg k
  -- multiply inequality by nonneg left factor
  have : B_of k * 1 ≤ B_of k * B_of m := mul_le_mul_of_nonneg_left h1 hnonneg
  simpa [this, mul_comm, mul_left_comm, mul_assoc] using this

/-! ### Strict step growth for `B_of` -/

lemma B_of_lt_succ (k : Nat) : B_of k < B_of (k + 1) := by
  have hkpos : 0 < B_of k := B_of_pos k
  have h12 : (1 : ℝ) < 2 := by norm_num
  calc
    B_of k = 1 * B_of k := by simp
    _ < 2 * B_of k := by exact mul_lt_mul_of_pos_right h12 hkpos
    _ = B_of (k + 1) := by simpa [B_of_succ, mul_comm]

/-- Two to an integer power: 2^k for k ∈ ℤ. -/
noncomputable def twoPowZ (k : Int) : ℝ :=
  if 0 ≤ k then (2 : ℝ) ^ (Int.toNat k)
  else 1 / ((2 : ℝ) ^ (Int.toNat (-k)))

@[simp] lemma twoPowZ_zero : twoPowZ 0 = 1 := by simp [twoPowZ]
@[simp] lemma twoPowZ_ofNat (k : Nat) : twoPowZ (Int.ofNat k) = (2 : ℝ) ^ k := by simp [twoPowZ]
@[simp] lemma twoPowZ_negSucc (k : Nat) : twoPowZ (Int.negSucc k) = 1 / ((2 : ℝ) ^ k.succ) := by
  simp [twoPowZ]

lemma twoPowZ_pos (k : Int) : 0 < twoPowZ k := by
  unfold twoPowZ
  by_cases h : 0 ≤ k
  · have h2 : 0 < (2 : ℝ) := by norm_num
    have : 0 < (2 : ℝ) ^ (Int.toNat k) := by simpa using pow_pos h2 (Int.toNat k)
    simpa [h] using this
  · have h2 : 0 < (2 : ℝ) := by norm_num
    have : 0 < (2 : ℝ) ^ (Int.toNat (-k)) := by simpa using pow_pos h2 (Int.toNat (-k))
    have : 0 < 1 / ((2 : ℝ) ^ (Int.toNat (-k))) := by
      exact div_pos (by norm_num) this
    simpa [h] using this

/-- φ-power wrapper. -/
noncomputable def PhiPow (x : ℝ) : ℝ := Real.exp (Real.log (Constants.phi) * x)

lemma PhiPow_add (x y : ℝ) : PhiPow (x + y) = PhiPow x * PhiPow y := by
  unfold PhiPow
  have hx : Real.log (Constants.phi) * (x + y)
            = Real.log (Constants.phi) * x + Real.log (Constants.phi) * y := by ring
  have := Real.exp_add (Real.log (Constants.phi) * x) (Real.log (Constants.phi) * y)
  simpa [hx, mul_comm, mul_left_comm, mul_assoc]
    using this

lemma PhiPow_sub (x y : ℝ) : PhiPow (x - y) = PhiPow x / PhiPow y := by
  unfold PhiPow
  have hx : Real.log (Constants.phi) * (x - y)
            = Real.log (Constants.phi) * x + Real.log (Constants.phi) * (-y) := by ring
  calc
    Real.exp (Real.log (Constants.phi) * (x - y))
        = Real.exp (Real.log (Constants.phi) * x + Real.log (Constants.phi) * (-y)) := by
              simpa [hx]
    _   = Real.exp (Real.log (Constants.phi) * x) * Real.exp (Real.log (Constants.phi) * (-y)) :=
              Real.exp_add _ _
    _   = Real.exp (Real.log (Constants.phi) * x) * (Real.exp (Real.log (Constants.phi) * y))⁻¹ := by
              simp [Real.exp_neg]
    _   = Real.exp (Real.log (Constants.phi) * x) / Real.exp (Real.log (Constants.phi) * y) := by
              simp [div_eq_mul_inv]

@[simp] lemma PhiPow_zero : PhiPow 0 = 1 := by
  unfold PhiPow
  simp

@[simp] lemma PhiPow_one : PhiPow 1 = Constants.phi := by
  unfold PhiPow
  have hφ : 0 < Constants.phi := Constants.phi_pos
  simp [one_mul, Real.exp_log hφ]

@[simp] lemma PhiPow_neg (y : ℝ) : PhiPow (-y) = 1 / PhiPow y := by
  have := PhiPow_sub 0 y
  simpa [PhiPow_zero, sub_eq_add_neg] using this

lemma PhiPow_pos (x : ℝ) : 0 < PhiPow x := by
  unfold PhiPow
  simpa using Real.exp_pos (Real.log (Constants.phi) * x)

@[simp] noncomputable def lambdaA : ℝ := Real.log Constants.phi
@[simp] noncomputable def kappaA  : ℝ := Constants.phi

@[simp] noncomputable def F_ofZ (Z : ℤ) : ℝ := (Real.log (1 + (Z : ℝ) / kappaA)) / lambdaA

@[simp] lemma F_ofZ_zero : F_ofZ 0 = 0 := by
  simp [F_ofZ]

@[simp] def Z_quark (Q : ℤ) : ℤ := 4 + (6 * Q) ^ (2 : Nat) + (6 * Q) ^ (4 : Nat)
@[simp] def Z_lepton (Q : ℤ) : ℤ := (6 * Q) ^ (2 : Nat) + (6 * Q) ^ (4 : Nat)
@[simp] def Z_neutrino : ℤ := 0

lemma kappaA_pos : 0 < kappaA := by
  unfold kappaA
  simpa using Constants.phi_pos

lemma lambdaA_pos : 0 < lambdaA := by
  unfold lambdaA
  have : 1 < Constants.phi := Constants.one_lt_phi
  simpa using (Real.log_pos_iff.mpr this)

lemma lambdaA_ne_zero : lambdaA ≠ 0 := by
  exact ne_of_gt lambdaA_pos

lemma kappaA_ne_zero : kappaA ≠ 0 := by
  simpa [kappaA] using Constants.phi_ne_zero

/-- Monotonicity of `PhiPow`: it is increasing in its argument. -/
lemma PhiPow_mono {x y : ℝ} (hxy : x ≤ y) : PhiPow x ≤ PhiPow y := by
  unfold PhiPow
  have a_pos : 0 < Real.log Constants.phi := by
    simpa [lambdaA] using lambdaA_pos
  have : Real.log Constants.phi * x ≤ Real.log Constants.phi * y :=
    mul_le_mul_of_nonneg_left hxy (le_of_lt a_pos)
  exact (Real.exp_le_exp.mpr this)

/-- Strict monotonicity of `PhiPow`. -/
lemma PhiPow_strict_mono {x y : ℝ} (hxy : x < y) : PhiPow x < PhiPow y := by
  unfold PhiPow
  have a_pos : 0 < Real.log Constants.phi := by
    simpa [lambdaA] using lambdaA_pos
  have : Real.log Constants.phi * x < Real.log Constants.phi * y :=
    mul_lt_mul_of_pos_left hxy a_pos
  exact (Real.exp_lt_exp.mpr this)

/-! Ledger units (δ subgroup) -/
namespace LedgerUnits

/-- The subgroup of ℤ generated by δ. We specialize to δ = 1 for a clean order isomorphism. -/
def DeltaSub (δ : ℤ) := {x : ℤ // ∃ n : ℤ, x = n * δ}

/-- Embed ℤ into the δ=1 subgroup. -/
def fromZ_one (n : ℤ) : DeltaSub 1 := ⟨n, by exact ⟨n, by simpa using (Int.mul_one n)⟩⟩

/-- Project from the δ=1 subgroup back to ℤ by taking its value. -/
def toZ_one (p : DeltaSub 1) : ℤ := p.val

@[simp] lemma toZ_fromZ_one (n : ℤ) : toZ_one (fromZ_one n) = n := rfl

@[simp] lemma fromZ_toZ_one (p : DeltaSub 1) : fromZ_one (toZ_one p) = p := by
  cases p with
  | mk x hx =>
    apply Subtype.ext
    rfl

/-- Explicit equivalence between the δ=1 subgroup and ℤ (mapping n·1 ↦ n). -/
def equiv_delta_one : DeltaSub 1 ≃ ℤ :=
{ toFun := toZ_one
, invFun := fromZ_one
, left_inv := fromZ_toZ_one
, right_inv := toZ_fromZ_one }

end LedgerUnits

end RS
end RH
end IndisputableMonolith
