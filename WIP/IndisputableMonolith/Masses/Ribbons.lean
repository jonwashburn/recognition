import Mathlib

namespace IndisputableMonolith
namespace Masses
namespace Ribbons

/-- Gauge tags used in the word constructor. -/
inductive GaugeTag | Y | T3 | Color
deriving DecidableEq, Repr

/-- Eight‑tick clock. -/
abbrev Tick := Fin 8

/-- A ribbon syllable on the eight‑tick clock. -/
structure Ribbon where
  start : Tick
  dir   : Bool   -- true = +, false = −
  bit   : Int    -- intended ±1
  tag   : GaugeTag
deriving Repr, DecidableEq

/-- Inverse ribbon: flip direction and ledger bit. -/
@[simp] def inv (r : Ribbon) : Ribbon := { r with dir := ! r.dir, bit := - r.bit }

/-- Cancellation predicate for adjacent syllables (tick consistency abstracted). -/
@[simp] def cancels (a b : Ribbon) : Bool := (b.dir = ! a.dir) ∧ (b.bit = - a.bit) ∧ (b.tag = a.tag)

/-- Neutral commutation predicate for adjacent syllables. Swapping preserves
ledger additivity and winding by construction; we additionally require the
start ticks to differ to avoid degenerate swaps. -/
@[simp] def neutralCommute (a b : Ribbon) : Bool := a.start ≠ b.start

/-- A word is a list of ribbon syllables. -/
abbrev Word := List Ribbon

/-- Deterministic ring pattern for a given tag: spread across ticks, alternate direction. -/
def ringSeq (tag : GaugeTag) (n : Nat) : Word :=
  (List.range n).map (fun k =>
    let t : Tick := ⟨k % 8, by have : (k % 8) < 8 := Nat.mod_lt _ (by decide); simpa using this⟩
    let d := k % 2 = 0
    { start := t, dir := d, bit := 1, tag := tag })

/-- One left‑to‑right cancellation pass: drop the first adjacent cancelling pair if present. -/
def rewriteOnce : Word → Word
| [] => []
| [a] => [a]
| a :: b :: rest =>
    if cancels a b then
      rest
    else if neutralCommute a b ∧ (a.tag, a.start, a.dir, a.bit) > (b.tag, b.start, b.dir, b.bit) then
      -- perform a neutral swap to drive toward a canonical order
      b :: a :: rest
    else
      a :: rewriteOnce (b :: rest)

/-- Normalization via bounded passes: at most length passes strictly reduce on success. -/
def normalForm (w : Word) : Word :=
  let n := w.length
  let fuel := n * n + n
  let rec loop : Nat → Word → Word
  | 0, acc => acc
  | Nat.succ k, acc =>
      let acc' := rewriteOnce acc
      if acc' = acc then acc else loop k acc'
  loop fuel w

/-- Reduced length ℓ(W) as length of the normal form. -/
@[simp] def ell (w : Word) : Nat := (normalForm w).length

/-- Net winding on the eight‑tick clock (abstracted): +1 for dir, −1 otherwise. -/
def winding (w : Word) : Int :=
  (w.map (fun r => if r.dir then (1 : Int) else (-1 : Int))).foldl (·+·) 0

/-- Proper mod‑8 torsion quotient. -/
abbrev Torsion8 := ZMod 8

/-- Torsion class via ZMod 8. -/
@[simp] def torsion8 (w : Word) : Torsion8 := (winding w : Int)

/-- WIP local generation class for standalone check. -/
inductive GenClass | g1 | g2 | g3
deriving DecidableEq, Repr

/-- Map mod‑8 torsion to a 3‑class generation label (WIP local). -/
@[simp] def genOfTorsion (t : Torsion8) : GenClass :=
  match (t.val % 3) with
  | 0 => GenClass.g1
  | 1 => GenClass.g2
  | _ => GenClass.g3

/-- WIP local rung view for standalone check. -/
structure RungSpec where
  ell : Nat
  gen : GenClass

/-- Build rung from word and a generation class (WIP: return ℤ from length). -/
@[simp] def rungFrom (gen : GenClass) (w : Word) : ℤ :=
  (ell w : Nat)

/-- WIP local Z-charge helpers. -/
@[simp] def Z_quark (Q : ℤ) : ℤ := 0
@[simp] def Z_lepton (Q : ℤ) : ℤ := 0

/-- Word‑charge from integerized charge (Q6=6Q) and sector flag. -/
@[simp] def Z_of_charge (isQuark : Bool) (Q6 : ℤ) : ℤ :=
  if isQuark then Z_quark Q6 else Z_lepton Q6

/-- Canonical pure mass from word, generation class, and charge (WIP: stub 0). -/
@[simp] def massCanonFromWord (isQuark : Bool) (Q6 : ℤ)
  (gen : GenClass) (w : Word) : ℝ := 0

end Ribbons
end Masses
end IndisputableMonolith
