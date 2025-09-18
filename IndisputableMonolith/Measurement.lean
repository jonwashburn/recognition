import Mathlib
import IndisputableMonolith.Streams

namespace IndisputableMonolith
namespace Measurement

open Classical
open Streams
open scoped BigOperators

/-- Sum of one 8‑tick sub‑block starting at index `j*8`. -/
def subBlockSum8 (s : Stream) (j : Nat) : Nat :=
  ∑ i : Fin 8, (if s (j * 8 + i.val) then 1 else 0)

/-- On any stream lying in the cylinder of an 8‑bit window, the aligned
    first block sum (j=0; T=8k alignment) equals the window integer `Z`. -/
lemma firstBlockSum_eq_Z_on_cylinder (w : Pattern 8) {s : Stream}
  (hs : s ∈ Cylinder w) :
  subBlockSum8 s 0 = Z_of_window w := by
  classical
  -- Reduce the sub‑block to the first 8 ticks.
  have hsum : subBlockSum8 s 0 = sumFirst 8 s := by
    unfold subBlockSum8 sumFirst
    simp [Nat.zero_mul, zero_add]
  -- Apply the cylinder lemma for the first‑8 sum.
  simpa [hsum] using
    (sumFirst_eq_Z_on_cylinder (n:=8) w (s:=s) hs)

/-- For periodic extensions of an 8‑bit window, each sub‑block sums to `Z`. -/
lemma subBlockSum8_periodic_eq_Z (w : Pattern 8) (j : Nat) :
  subBlockSum8 (extendPeriodic8 w) j = Z_of_window w := by
  classical
  unfold subBlockSum8 Z_of_window extendPeriodic8
  -- For `i : Fin 8`, we have `(j*8 + i) % 8 = i`.
  have hmod : ∀ i : Fin 8, ((j * 8 + i.val) % 8) = i.val := by
    intro i
    -- (a*8 + b) % 8 = b when b < 8
    have : (j * 8) % 8 = 0 := by simpa using Nat.mul_mod j 8 8
    have hi : i.val % 8 = i.val := Nat.mod_eq_of_lt i.isLt
    calc
      (j * 8 + i.val) % 8
          = ((j * 8) % 8 + i.val % 8) % 8 := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
                  (Nat.add_mod (j*8) i.val 8)
      _   = (0 + i.val) % 8 := by simpa [this, hi]
      _   = i.val % 8 := by simp
      _   = i.val := by simpa [hi]
  -- Rewrite each summand to the window bit.
  refine (congrArg (fun f => ∑ i : Fin 8, f i) ?_)
  funext i
  simp [extendPeriodic8_eq_mod, hmod i]

/-- Aligned block sum over `k` copies of the 8‑tick window (so instrument length `T=8k`). -/
def blockSumAligned8 (k : Nat) (s : Stream) : Nat :=
  ∑ j : Fin k, subBlockSum8 s j.val

lemma sum_const_nat {α} (s : Finset α) (c : Nat) :
  (∑ _i in s, c) = s.card * c := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have : (insert a s).card = s.card + 1 := by simpa [Finset.card_insert_of_not_mem ha]
    simp [Finset.sum_insert, ha, ih, this, Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- For `s = extendPeriodic8 w`, summing `k` aligned 8‑blocks yields `k * Z(w)`. -/
lemma blockSumAligned8_periodic (w : Pattern 8) (k : Nat) :
  blockSumAligned8 k (extendPeriodic8 w) = k * Z_of_window w := by
  classical
  unfold blockSumAligned8
  have hconst : ∀ j : Fin k, subBlockSum8 (extendPeriodic8 w) j.val = Z_of_window w := by
    intro j; simpa using subBlockSum8_periodic_eq_Z w j.val
  have := congrArg (fun f => ∑ j : Fin k, f j) (funext hconst)
  -- Sum of a constant over `Fin k` equals `k * Z`.
  simpa [sum_const_nat, Finset.card_univ] using this

/-- Averaged (per‑window) observation equals `Z` on periodic extensions. -/
def observeAvg8 (k : Nat) (s : Stream) : Nat :=
  blockSumAligned8 k s / k

/-- DNARP Eq. (blockSum=Z at T=8k): on the periodic extension of an 8‑bit window,
    the per‑window averaged observation equals the window integer `Z`. -/
lemma observeAvg8_periodic_eq_Z {k : Nat} (hk : k ≠ 0) (w : Pattern 8) :
  observeAvg8 k (extendPeriodic8 w) = Z_of_window w := by
  classical
  unfold observeAvg8
  have hsum := blockSumAligned8_periodic w k
  have : (k * Z_of_window w) / k = Z_of_window w := by
    exact Nat.mul_div_cancel_left (Z_of_window w) (Nat.pos_of_ne_zero hk)
  simpa [hsum, this]

end Measurement
end IndisputableMonolith
