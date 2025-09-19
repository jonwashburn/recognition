import Mathlib

namespace IndisputableMonolith
namespace Ethics

noncomputable section
open Classical

universe w

/-- A minimal cost model over actions of type `A`. Costs are nonnegative reals. -/
structure CostModel (A : Type u) where
  cost : A → ℝ
  nonneg : ∀ a, 0 ≤ cost a

variable {A : Type u}

/-- Ethical preference: `a ≼ b` iff `cost a ≤ cost b` (lower cost is better). -/
def Prefer (M : CostModel A) (a b : A) : Prop := M.cost a ≤ M.cost b

infix:50 "≼" => Prefer

/-- Net improvement predicate: `a` strictly improves on `b`. -/
def Improves (M : CostModel A) (a b : A) : Prop := M.cost a < M.cost b

/-- Reflexivity: every action is at least as good as itself. -/
lemma prefer_refl (M : CostModel A) (a : A) : a ≼[M] a := by
  dsimp [Prefer]
  exact le_rfl

/-- Transitivity: if `a ≼ b` and `b ≼ c`, then `a ≼ c`. -/
lemma prefer_trans (M : CostModel A) {a b c : A}
  (hab : a ≼[M] b) (hbc : b ≼[M] c) : a ≼[M] c := by
  dsimp [Prefer] at hab hbc ⊢; exact le_trans hab hbc

/-- Preorder instance for preference. -/
instance (M : CostModel A) : Preorder A where
  le := Prefer M
  le_refl := prefer_refl (M:=M)
  le_trans := prefer_trans (M:=M)

/-- Composable actions under a cost model: binary composition with subadditivity and monotonicity. -/
structure Composable (M : CostModel A) where
  comp : A → A → A
  subadd : ∀ a b, M.cost (comp a b) ≤ M.cost a + M.cost b
  mono : ∀ a a' b b', a ≼[M] a' → b ≼[M] b' → comp a b ≼[M] comp a' b'
  strict_mono_left : ∀ a a' x, Improves M a a' → Improves M (comp a x) (comp a' x)

/-- Monotonicity of composition w.r.t. preference. -/
theorem prefer_comp_mono (M : CostModel A) (C : Composable M)
  {a₁ a₂ b₁ b₂ : A}
  (ha : a₁ ≼[M] a₂) (hb : b₁ ≼[M] b₂) :
  C.comp a₁ b₁ ≼[M] C.comp a₂ b₂ := by
  dsimp [Prefer] at ha hb ⊢
  exact C.mono a₁ a₂ b₁ b₂ ha hb

/-- Composition preserves improvement. -/
theorem improves_comp_left (M : CostModel A) (C : Composable M)
  {a b x : A} (h : Improves M a b) : Improves M (C.comp a x) (C.comp b x) := by
  exact C.strict_mono_left a b x h

/-- CQ alignment at threshold θ ∈ [0,1]: score ≥ θ. -/
/- Placeholder for Measurement.CQ dependency -/
axiom CQ : Type
axiom score : CQ → ℝ
def CQAligned (θ : ℝ) (c : CQ) : Prop :=
  0 ≤ θ ∧ θ ≤ 1 ∧ score c ≥ θ

/-- Ethical admissibility under 45‑gap: either no experience required, or the plan includes experience. -/
/- Placeholder for Gap45 dependency -/
axiom requiresExperience : CQ → Nat → Prop
def Admissible (period : Nat) (c : CQ) (hasExperience : Prop) : Prop :=
  ¬ requiresExperience c period ∨ hasExperience

/-- Prefer alignment: higher CQ never hurts in the costless tie (axiom placeholder to be specialized). -/
/-- Prefer higher CQ does not break ties: if costs are equal and `c₁` is at least as aligned as `c₂`,
    then `a` is preferred to `b`. -/
theorem prefer_by_cq (M : CostModel A) (a b : A) (c₁ c₂ : CQ) (θ : ℝ)
  (ht : 0 ≤ θ ∧ θ ≤ 1) (hc : CQAligned θ c₂ → CQAligned θ c₁)
  (hcost : M.cost a = M.cost b) : a ≼[M] b := by
  dsimp [Prefer]
  simpa [hcost]

/-- Lexicographic ethical preference with admissibility first, then cost preference. -/
def PreferLex (M : CostModel A) (period : Nat) (cq : CQ)
  (hasExpA hasExpB : Prop) (a b : A) : Prop :=
  (Admissible period cq hasExpA ∧ ¬ Admissible period cq hasExpB)
  ∨ (Admissible period cq hasExpA ∧ Admissible period cq hasExpB ∧ a ≼[M] b)

end

end Ethics
end IndisputableMonolith
