import Mathlib

namespace IndisputableMonolith
namespace Recognition

/-! ### T1 (MP): Nothing cannot recognize itself -/

abbrev Nothing := Empty

/-- Minimal recognizer→recognized pairing. -/
structure Recognize (A : Type) (B : Type) : Type where
  recognizer : A
  recognized : B

/-- MP: It is impossible for Nothing to recognize itself. -/
def MP : Prop := ¬ ∃ _ : Recognize Nothing Nothing, True

theorem mp_holds : MP := by
  intro h
  rcases h with ⟨⟨r, _⟩, _⟩
  cases r

structure RecognitionStructure where
  U : Type
  R : U → U → Prop

structure Chain (M : RecognitionStructure) where
  n : Nat
  f : Fin (n+1) → M.U
  ok : ∀ i : Fin n, M.R (f i.castSucc) (f i.succ)

namespace Chain
variable {M : RecognitionStructure} (ch : Chain M)
def head : M.U := by
  have hpos : 0 < ch.n + 1 := Nat.succ_pos _
  exact ch.f ⟨0, hpos⟩
def last : M.U := by
  have hlt : ch.n < ch.n + 1 := Nat.lt_succ_self _
  exact ch.f ⟨ch.n, hlt⟩
end Chain

structure Ledger (M : RecognitionStructure) where
  debit : M.U → ℤ
  credit : M.U → ℤ

def phi {M} (L : Ledger M) : M.U → ℤ := fun u => L.debit u - L.credit u

def chainFlux {M} (L : Ledger M) (ch : Chain M) : ℤ :=
  phi L (Chain.last ch) - phi L (Chain.head ch)

class Conserves {M} (L : Ledger M) : Prop where
  conserve : ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0

lemma chainFlux_zero_of_loop {M} (L : Ledger M) [Conserves L] (ch : Chain M) (h : ch.head = ch.last) :
  chainFlux L ch = 0 := Conserves.conserve L ch h

lemma phi_zero_of_balanced {M} (L : Ledger M) (hbal : ∀ u, L.debit u = L.credit u) :
  ∀ u, phi L u = 0 := by
  intro u; simp [phi, hbal u, sub_self]

lemma chainFlux_zero_of_balanced {M} (L : Ledger M) (ch : Chain M)
  (hbal : ∀ u, L.debit u = L.credit u) :
  chainFlux L ch = 0 := by
  simp [chainFlux, phi_zero_of_balanced (M:=M) L hbal]

class AtomicTick (M : RecognitionStructure) where
  postedAt : Nat → M.U → Prop
  unique_post : ∀ t : Nat, ∃! u : M.U, postedAt t u

theorem T2_atomicity {M} [AtomicTick M] :
  ∀ t u v, AtomicTick.postedAt (M:=M) t u → AtomicTick.postedAt (M:=M) t v → u = v := by
  intro t u v hu hv
  rcases (AtomicTick.unique_post (M:=M) t) with ⟨w, hw, huniq⟩
  exact huniq u w hu hw ▸ huniq v w hv hw ▸ rfl

end Recognition

namespace Demo

open Recognition

structure U where
  a : Unit

def recog : U → U → Prop := fun _ _ => True

def M : RecognitionStructure := { U := U, R := recog }

def L : Ledger M := { debit := fun _ => 1, credit := fun _ => 1 }

def twoStep : Chain M :=
  { n := 1
  , f := fun _ => ⟨()⟩
  , ok := by intro i; trivial }

example : chainFlux L twoStep = 0 := by
  haveI : Conserves L :=
    { conserve := by
        intro ch h; simp [chainFlux, phi, Recognition.Chain.head, Recognition.Chain.last, h] }
  have hloop : twoStep.head = twoStep.last := rfl
  simpa [hloop] using (chainFlux_zero_of_loop L twoStep hloop)

end Demo

/‑! ## Nontrivial modeling instances: concrete `AtomicTick` examples -/
namespace ModelingExamples

open Recognition

/-- A simple 2‑vertex recognition structure with bidirectional relation. -/
def SimpleStructure : Recognition.RecognitionStructure :=
  { U := Bool
  , R := fun a b => a ≠ b }

/-- Deterministic posting schedule: the unique poster at time `t` is `(t % 2 == 1)`. -/
def SimpleTicks : Nat → Bool → Prop := fun t v => v = (t % 2 == 1)

instance : Recognition.AtomicTick SimpleStructure :=
  { postedAt := SimpleTicks
  , unique_post := by
      intro t
      refine ⟨(t % 2 == 1), rfl, ?uniq⟩
      intro u hu
      simpa [SimpleTicks] using hu }

/-- A 3‑cycle recognition structure on `Fin 3`. -/
def Cycle3 : Recognition.RecognitionStructure :=
  { U := Fin 3
  , R := fun i j => j = ⟨(i.val + 1) % 3, by
                        have : (i.val + 1) % 3 < 3 := by
                          have : (i.val + 1) % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
                          simpa using this
                        exact this⟩ }

/-- Unique poster at time `t` is the residue class `t % 3`. -/
def Cycle3Ticks : Nat → (Fin 3) → Prop := fun t v => v.val = t % 3

instance : Recognition.AtomicTick Cycle3 :=
  { postedAt := Cycle3Ticks
  , unique_post := by
      intro t
      refine ⟨⟨t % 3, by exact Nat.mod_lt _ (by decide : 0 < 3)⟩, ?posted, ?uniq⟩
      · rfl
      · intro u hu
        -- Coerce equality on values to equality in `Fin 3`.
        apply Fin.ext
        simpa [Cycle3Ticks] using hu }

end ModelingExamples

end IndisputableMonolith
