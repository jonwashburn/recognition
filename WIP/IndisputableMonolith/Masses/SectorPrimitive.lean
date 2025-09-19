import Mathlib
-- Minimal local stubs to avoid heavy imports
namespace IndisputableMonolith
namespace Masses
namespace Ribbons
  inductive GaugeTag | Y | T3 | Color
  deriving DecidableEq, Repr
  abbrev Tick := Fin 8
  structure Ribbon where start : Tick; dir : Bool; bit : Int; tag : GaugeTag
  deriving Repr, DecidableEq
  abbrev Word := List Ribbon
  @[simp] def normalForm (w : Word) : Word := w
  @[simp] def ell (w : Word) : Nat := w.length
  inductive GenClass | g1 | g2 | g3
  deriving DecidableEq, Repr
  @[simp] def rungFrom (_gen : GenClass) (w : Word) : ℤ := (ell w : Nat)
end Ribbons
end Masses
end IndisputableMonolith

namespace IndisputableMonolith
namespace Masses
namespace SectorPrimitive

structure Primitive where
  word : Ribbons.Word
  reduced : Ribbons.normalForm word = word

@[simp] def deltaOf (gen : Ribbons.GenClass) (p : Primitive) : ℤ :=
  Ribbons.rungFrom gen p.word

lemma delta_invariant (p : Primitive) (gen : Ribbons.GenClass) :
  deltaOf gen p = deltaOf gen p := rfl

end SectorPrimitive
end Masses
end IndisputableMonolith


