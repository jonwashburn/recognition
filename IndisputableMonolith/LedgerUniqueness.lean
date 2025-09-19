import Mathlib
import IndisputableMonolith.Recognition
-- For standalone WIP, inline a minimal Kinematics to avoid module dependency
namespace Local
structure Kinematics (α : Type) where
  step : α → α → Prop
inductive ReachN {α} (K : Kinematics α) : Nat → α → α → Prop
| zero {x} : ReachN K 0 x x
| succ {n x y z} : ReachN K n x y → K.step y z → ReachN K (n+1) x z
def inBall {α} (K : Kinematics α) (x : α) (n : Nat) (y : α) : Prop := ∃ k ≤ n, ReachN K k x y
def Reaches {α} (K : Kinematics α) (x y : α) : Prop := ∃ n, ReachN K n x y
end Local

namespace IndisputableMonolith
namespace LedgerUniqueness

open Recognition

variable {M : Recognition.RecognitionStructure}

def IsAffine (δ : ℤ) (L : Recognition.Ledger M) : Prop :=
  True  -- WIP stub: replace with Potential.DE (phi L) when ported

axiom unique_on_reachN {δ : ℤ} {L L' : Recognition.Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 : M.U} (hbase : Recognition.phi L x0 = Recognition.phi L' x0) :
  ∀ {n y}, Local.ReachN ({ step := M.R }) n x0 y →
    Recognition.phi L y = Recognition.phi L' y

axiom unique_on_inBall {δ : ℤ} {L L' : Recognition.Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 y : M.U} (hbase : Recognition.phi L x0 = Recognition.phi L' x0) {n : Nat}
  (hin : Local.inBall ({ step := M.R }) x0 n y) :
  Recognition.phi L y = Recognition.phi L' y

axiom unique_up_to_const_on_component {δ : ℤ} {L L' : Recognition.Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 : M.U} : ∃ c : ℤ, ∀ {y : M.U}, Local.Reaches ({ step := M.R }) x0 y →
    Recognition.phi L y = Recognition.phi L' y + c

end LedgerUniqueness
end IndisputableMonolith


