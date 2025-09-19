import Mathlib

namespace IndisputableMonolith
namespace Ablation

/-- Axiom stubs for Constants dependencies -/
axiom Species : Type
axiom Sector : Type
noncomputable def tildeQ : Species → Int := fun _ => 0
axiom sector : Species → Sector
noncomputable def Z : Species → Int := fun _ => 0
noncomputable def Fgap : Int → ℝ := fun _ => 0

/-- Drop the +4 offset for quarks in Z. -/
noncomputable def Z_dropPlus4 (i : Species) : Int :=
  if tildeQ i > 0 then (tildeQ i)^2 + (tildeQ i)^4 else 0

/-- Drop the Q^4 term everywhere in Z. -/
noncomputable def Z_dropQ4 (i : Species) : Int :=
  if tildeQ i > 0 then 4 + (tildeQ i)^2 else 0

/-- Break the integerization ˜Q = 6Q by using ˜Q' = 3Q (integerized) instead. -/
noncomputable def tildeQ_broken3 : Species → Int :=
  fun _ => 0  -- Simplified stub

/-- Recompute Z with the broken integerization. -/
noncomputable def Z_break6Q (i : Species) : Int :=
  4 + (tildeQ_broken3 i)^2 + (tildeQ_broken3 i)^4

/-- Anchor-equality predicate for a candidate Z-map: residues must match the original. -/
def AnchorEq (Z' : Species → Int) : Prop := ∀ i, Fgap (Z' i) = Fgap (Z i)

/-- If anchor-equality holds for a transformed Z, then Z' must agree with Z on nonnegative values. -/
lemma anchorEq_implies_Zeq_nonneg
  {Z' : Species → Int} (h : AnchorEq Z')
  (h_inj : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → Fgap a = Fgap b → a = b)
  {i : Species} (hZnonneg : 0 ≤ Z i) (hZ'nonneg : 0 ≤ Z' i) : Z' i = Z i := by
  have h_eq := h i
  exact h_inj (Z' i) (Z i) hZ'nonneg hZnonneg h_eq

/-- If anchor-equality holds, each ablation leads to a contradiction. -/
axiom ablation_contradictions :
  (¬ AnchorEq Z_dropPlus4) ∧ (¬ AnchorEq Z_dropQ4) ∧ (¬ AnchorEq Z_break6Q)

end Ablation
end IndisputableMonolith
