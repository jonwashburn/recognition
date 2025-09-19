import Mathlib

namespace IndisputableMonolith
namespace Masses
namespace Ribbons

inductive GaugeTag | Y | T3 | Color
deriving DecidableEq, Repr

abbrev Tick := Fin 8

structure Ribbon where
  start : Tick
  dir   : Bool
  bit   : Int
  tag   : GaugeTag
deriving Repr, DecidableEq

@[simp] def inv (r : Ribbon) : Ribbon := { r with dir := ! r.dir, bit := - r.bit }

@[simp] def cancels (a b : Ribbon) : Bool := (b.dir = ! a.dir) ∧ (b.bit = - a.bit) ∧ (b.tag = a.tag)

@[simp] def neutralCommute (a b : Ribbon) : Bool := a.start ≠ b.start

abbrev Word := List Ribbon

def ringSeq (tag : GaugeTag) (n : Nat) : Word :=
  (List.range n).map (fun k =>
    let t : Tick := ⟨k % 8, by have : (k % 8) < 8 := Nat.mod_lt _ (by decide); simpa using this⟩
    let d := k % 2 = 0
    { start := t, dir := d, bit := 1, tag := tag })

def rewriteOnce : Word → Word
| [] => []
| [a] => [a]
| a :: b :: rest =>
    if cancels a b then rest
    else if neutralCommute a b then b :: a :: rest
    else a :: rewriteOnce (b :: rest)

def normalForm (w : Word) : Word :=
  let n := w.length
  let fuel := n * n + n
  let rec loop : Nat → Word → Word
  | 0, acc => acc
  | Nat.succ k, acc =>
      let acc' := rewriteOnce acc
      if acc' = acc then acc else loop k acc'
  loop fuel w

@[simp] def ell (w : Word) : Nat := (normalForm w).length

def winding (w : Word) : Int :=
  (w.map (fun r => if r.dir then (1 : Int) else (-1 : Int))).foldl (·+·) 0

abbrev Torsion8 := ZMod 8

@[simp] def torsion8 (w : Word) : Torsion8 := (winding w : Int)

inductive GenClass | g1 | g2 | g3
deriving DecidableEq, Repr

@[simp] def genOfTorsion (t : Torsion8) : GenClass :=
  match (t.val % 3) with
  | 0 => GenClass.g1
  | 1 => GenClass.g2
  | _ => GenClass.g3

structure RungSpec where
  ell : Nat
  gen : GenClass

@[simp] def rungFrom (gen : GenClass) (w : Word) : ℤ := (ell w : Nat)

@[simp] def Z_quark (_Q : ℤ) : ℤ := 0
@[simp] def Z_lepton (_Q : ℤ) : ℤ := 0

@[simp] def Z_of_charge (isQuark : Bool) (Q6 : ℤ) : ℤ := if isQuark then Z_quark Q6 else Z_lepton Q6

@[simp] def massCanonFromWord (_isQuark : Bool) (_Q6 : ℤ) (_gen : GenClass) (_w : Word) : ℝ := 0

end Ribbons
end Masses
end IndisputableMonolith
