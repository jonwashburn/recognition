import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace RSBridge

inductive Sector | up | down | lepton | neutrino
deriving DecidableEq, Repr

inductive Fermion
| d | s | b | u | c | t | e | mu | tau | nu1 | nu2 | nu3
deriving DecidableEq, Repr, Inhabited

def sectorOf : Fermion → Sector
| .d | .s | .b => .down
| .u | .c | .t => .up
| .e | .mu | .tau => .lepton
| .nu1 | .nu2 | .nu3 => .neutrino

def tildeQ : Fermion → ℤ
| .u | .c | .t => 4
| .d | .s | .b => -2
| .e | .mu | .tau => -6
| .nu1 | .nu2 | .nu3 => 0

def ZOf (f : Fermion) : ℤ :=
  let q := tildeQ f
  match sectorOf f with
  | .up | .down => 4 + q*q + q*q*q*q
  | .lepton     =>     q*q + q*q*q*q
  | .neutrino   => 0

noncomputable def gap (Z : ℤ) : ℝ :=
  (Real.log (1 + (Z : ℝ) / (Constants.phi))) / (Real.log (Constants.phi))

notation "𝓕(" Z ")" => gap Z

def residueAtAnchor (f : Fermion) : ℝ := gap (ZOf f)

theorem anchorEquality (f : Fermion) : residueAtAnchor f = gap (ZOf f) := by rfl

theorem equalZ_residue (f g : Fermion) (hZ : ZOf f = ZOf g) :
  residueAtAnchor f = residueAtAnchor g := by
  simp [residueAtAnchor, hZ]

noncomputable def rung : Fermion → ℤ
| .e   => 2   | .mu  => 13  | .tau => 19
| .u   => 4   | .c   => 15  | .t   => 21
| .d   => 4   | .s   => 15  | .b   => 21
| .nu1 => 0   | .nu2 => 11  | .nu3 => 19

def M0 : ℝ := 1
theorem M0_pos : 0 < M0 := by norm_num

noncomputable def massAtAnchor (f : Fermion) : ℝ :=
  M0 * Real.exp (((rung f : ℝ) - 8 + gap (ZOf f)) * Real.log (Constants.phi))

theorem anchor_ratio (f g : Fermion) (hZ : ZOf f = ZOf g) :
  massAtAnchor f / massAtAnchor g =
    Real.exp (((rung f : ℝ) - rung g) * Real.log (Constants.phi)) := by
  unfold massAtAnchor
  set Af := ((rung f : ℝ) - 8 + gap (ZOf f)) * Real.log (Constants.phi)
  set Ag := ((rung g : ℝ) - 8 + gap (ZOf g)) * Real.log (Constants.phi)
  have hM : M0 ≠ 0 := ne_of_gt M0_pos
  calc
    (M0 * Real.exp Af) / (M0 * Real.exp Ag)
        = (Real.exp Af) / (Real.exp Ag) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (mul_div_mul_left (Real.exp Af) (Real.exp Ag) M0 hM)
    _ = Real.exp (Af - Ag) := by
              simpa [Real.exp_sub] using (Real.exp_sub Af Ag).symm
    _ = Real.exp ((((rung f : ℝ) - 8 + gap (ZOf f)) - ((rung g : ℝ) - 8 + gap (ZOf g)))
                   * Real.log (Constants.phi)) := by
              have : Af - Ag
                    = (((rung f : ℝ) - 8 + gap (ZOf f)) - ((rung g : ℝ) - 8 + gap (ZOf g)))
                       * Real.log (Constants.phi) := by
                        simp [Af, Ag, sub_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                              mul_add, add_mul, sub_eq_add_neg]
              have h' :
                ((rung f : ℝ) - 8 + gap (ZOf f)) - ((rung g : ℝ) - 8 + gap (ZOf g))
                = (rung f : ℝ) - rung g + (gap (ZOf f) - gap (ZOf g)) := by ring
              simpa [this, h']
    _ = Real.exp (((rung f : ℝ) - rung g) * Real.log (Constants.phi)) := by
              simpa [hZ, sub_self, add_zero, add_comm, add_left_comm, add_assoc, mul_add,
                     add_right_comm, mul_comm, mul_left_comm, mul_assoc]

structure ResidueCert where
  f  : Fermion
  lo hi : ℚ
  lo_le_hi : lo ≤ hi

def ResidueCert.valid (c : ResidueCert) : Prop :=
  (c.lo : ℝ) ≤ gap (ZOf c.f) ∧ gap (ZOf c.f) ≤ (c.hi : ℝ)

end RSBridge
end IndisputableMonolith
