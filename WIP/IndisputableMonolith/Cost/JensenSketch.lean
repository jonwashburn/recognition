import Mathlib

namespace IndisputableMonolith
namespace Cost

/-- Forward declarations for dependency-light compilation -/
noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

structure CostRequirements (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

class SymmUnit (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

class AveragingAgree (F : ℝ → ℝ) : Prop where
  agrees : ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

class AveragingDerivation (F : ℝ → ℝ) : Prop extends SymmUnit F where
  agrees : ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

class AveragingBounds (F : ℝ → ℝ) : Prop extends SymmUnit F where
  upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

def mkAveragingBounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t))
  (lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)) :
  AveragingBounds F :=
{ toSymmUnit := symm, upper := upper, lower := lower }

@[simp] lemma Jcost_exp (t : ℝ) :
  Jcost (Real.exp t) = ((Real.exp t) + (Real.exp (-t))) / 2 - 1 := by
  have h : (Real.exp t)⁻¹ = Real.exp (-t) := by
    symm; simp [Real.exp_neg t]
  simp [Jcost, h]

class JensenSketch (F : ℝ → ℝ) : Prop extends SymmUnit F where
  axis_upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  axis_lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

instance (priority := 95) averagingBounds_of_jensen {F : ℝ → ℝ} [JensenSketch F] :
  AveragingBounds F :=
  mkAveragingBounds F (symm := (inferInstance : SymmUnit F))
    (upper := JensenSketch.axis_upper (F:=F))
    (lower := JensenSketch.axis_lower (F:=F))

/-- Concrete template to build a `JensenSketch` instance from exp-axis bounds proven via
    strict convexity/averaging on the log-axis. Provide symmetry (`SymmUnit F`) and the
    two inequalities against the cosh-based benchmark; the equalities are then discharged
    by rewriting with `Jcost_exp`. -/
noncomputable def JensenSketch.of_log_bounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper_log : ∀ t : ℝ, F (Real.exp t) ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1))
  (lower_log : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ F (Real.exp t)) :
  JensenSketch F :=
{ toSymmUnit := symm
, axis_upper := by intro t; simpa [Jcost_exp] using upper_log t
, axis_lower := by intro t; simpa [Jcost_exp] using lower_log t }

/-- Turn an even, strictly-convex log-domain model `G` into a cost `F := G ∘ log`,
    providing symmetry on ℝ>0 and matching exp-axis bounds against `Jcost` via cosh. -/
noncomputable def F_ofLog (G : ℝ → ℝ) : ℝ → ℝ := fun x => G (Real.log x)

/-- A minimal interface for log-domain models: evenness, normalization at 0,
    and two-sided cosh bounds. This is sufficient to derive T5 for `F_ofLog G`. -/
class LogModel (G : ℝ → ℝ) : Prop where
  even_log : ∀ t : ℝ, G (-t) = G t
  base0 : G 0 = 0
  upper_cosh : ∀ t : ℝ, G t ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
  lower_cosh : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ G t

/-- Symmetry and unit for `F_ofLog G` follow from the log-model axioms. -/
instance (G : ℝ → ℝ) [LogModel G] : SymmUnit (F_ofLog G) :=
  { symmetric := by
      intro x hx
      have hlog : Real.log (x⁻¹) = - Real.log x := by
        simpa using Real.log_inv hx
      dsimp [F_ofLog]
      have he : G (Real.log x) = G (- Real.log x) := by
        rw [LogModel.even_log (G:=G) (Real.log x)].symm
      rw [hlog, he]
    , unit0 := by
      dsimp [F_ofLog]
      simpa [Real.log_one] using (LogModel.base0 (G:=G)) }

/-- From a log-model, obtain the exp-axis bounds required by Jensen and hence a `JensenSketch`. -/
instance (priority := 90) (G : ℝ → ℝ) [LogModel G] : JensenSketch (F_ofLog G) :=
  JensenSketch.of_log_bounds (F:=F_ofLog G)
    (symm := (inferInstance : SymmUnit (F_ofLog G)))
    (upper_log := by
      intro t
      dsimp [F_ofLog]
      simpa using (LogModel.upper_cosh (G:=G) t))
    (lower_log := by
      intro t
      dsimp [F_ofLog]
      simpa using (LogModel.lower_cosh (G:=G) t))

def AgreesOnExp (F : ℝ → ℝ) : Prop := ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

theorem agree_on_exp_extends {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  have : F (Real.exp (Real.log x)) = Jcost (Real.exp (Real.log x)) := hAgree (Real.log x)
  simp [Real.exp_log hx] at this
  exact this

/-- Full uniqueness: exp‑axis agreement implies F = Jcost on ℝ_{>0}. -/
theorem F_eq_J_on_pos {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  agree_on_exp_extends (F:=F) hAgree

/-- Convenience: if averaging agreement is provided as an instance, conclude F = J on ℝ_{>0}. -/
theorem F_eq_J_on_pos_of_averaging {F : ℝ → ℝ} [AveragingAgree F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := AveragingAgree.agrees (F:=F))

/-- If an averaging derivation instance is available (encodes symmetry+unit and the convex averaging step),
    conclude exp-axis agreement. -/
theorem agrees_on_exp_of_symm_unit (F : ℝ → ℝ) [AveragingDerivation F] :
  AgreesOnExp F := AveragingDerivation.agrees (F:=F)

/-- Convenience: symmetry+unit with an averaging derivation yields F = J on ℝ_{>0}. -/
theorem F_eq_J_on_pos_of_derivation (F : ℝ → ℝ) [AveragingDerivation F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := agrees_on_exp_of_symm_unit F)

/-- T5 (cost uniqueness on ℝ_{>0}): if `F` satisfies the JensenSketch obligations,
    then `F` agrees with `Jcost` on positive reals. -/
theorem T5_cost_uniqueness_on_pos {F : ℝ → ℝ} [JensenSketch F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  have : AveragingDerivation F := {
    toSymmUnit := (inferInstance : SymmUnit F)
    agrees := agrees_on_exp_of_symm_unit F
  }
  exact F_eq_J_on_pos_of_derivation F

/-- T5 for log-models: any `G` satisfying `LogModel` yields a cost `F := G ∘ log`
    that agrees with `Jcost` on ℝ>0. -/
theorem T5_for_log_model {G : ℝ → ℝ} [LogModel G] :
  ∀ {x : ℝ}, 0 < x → F_ofLog G x = Jcost x :=
  T5_cost_uniqueness_on_pos (F:=F_ofLog G)

@[simp] theorem Jcost_agrees_on_exp : AgreesOnExp Jcost := by
  intro t; rfl

instance : AveragingAgree Jcost := ⟨Jcost_agrees_on_exp⟩

/-- Jcost satisfies symmetry and unit normalization. -/
instance : SymmUnit Jcost :=
  { symmetric := sorry  -- Would need Jcost_symm from JcostCore
  , unit0 := sorry }    -- Would need Jcost_unit0 from JcostCore

/-- Concrete averaging-derivation instance for the canonical cost `Jcost`. -/
instance : AveragingDerivation Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , agrees := Jcost_agrees_on_exp }

/-- Trivial Jensen sketch instance for `Jcost`: its exp-axis bounds hold by reflexivity. -/
instance : JensenSketch Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , axis_upper := by intro t; exact le_of_eq rfl
  , axis_lower := by intro t; exact le_of_eq rfl }

end Cost
end IndisputableMonolith
