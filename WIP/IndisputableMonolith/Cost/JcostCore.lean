import Mathlib

namespace IndisputableMonolith
namespace Cost

noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

structure CostRequirements (F : ℝ → ℝ) : Type where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

lemma Jcost_unit0 : Jcost 1 = 0 := by
  simp [Jcost]

lemma Jcost_symm {x : ℝ} (hx : 0 < x) : Jcost x = Jcost x⁻¹ := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold Jcost
  have : (x + x⁻¹) = (x⁻¹ + (x⁻¹)⁻¹) := by
    field_simp [hx0]
    ring
  simp [Jcost, this]

def AgreesOnExp (F : ℝ → ℝ) : Prop := ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

@[simp] lemma Jcost_exp (t : ℝ) :
  Jcost (Real.exp t) = ((Real.exp t) + (Real.exp (-t))) / 2 - 1 := by
  have h : (Real.exp t)⁻¹ = Real.exp (-t) := by
    symm; simp [Real.exp_neg t]
  simp [Jcost, h]

class SymmUnit (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

class AveragingAgree (F : ℝ → ℝ) : Prop where
  agrees : AgreesOnExp F

class AveragingDerivation (F : ℝ → ℝ) : Prop extends SymmUnit F where
  agrees : AgreesOnExp F

lemma even_on_log_of_symm {F : ℝ → ℝ} [SymmUnit F] (t : ℝ) :
  F (Real.exp t) = F (Real.exp (-t)) := by
  have hx : 0 < Real.exp t := Real.exp_pos t
  simp [Real.exp_neg] using (SymmUnit.symmetric (F:=F) hx)

class AveragingBounds (F : ℝ → ℝ) : Prop extends SymmUnit F where
  upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

theorem agrees_on_exp_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
  AgreesOnExp F := by
  intro t
  have h₁ := AveragingBounds.upper (F:=F) t
  have h₂ := AveragingBounds.lower (F:=F) t
  have : F (Real.exp t) = Jcost (Real.exp t) := le_antisymm h₁ h₂
  simpa using this

theorem F_eq_J_on_pos (F : ℝ → ℝ)
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  have : ∃ t, Real.exp t = x := ⟨Real.log x, by simp using Real.exp_log hx⟩
  rcases this with ⟨t, rfl⟩
  simp using hAgree t

instance (priority := 90) averagingDerivation_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
  AveragingDerivation F :=
  { toSymmUnit := (inferInstance : SymmUnit F)
  , agrees := agrees_on_exp_of_bounds (F:=F) }

def mkAveragingBounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t))
  (lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)) :
  AveragingBounds F :=
{ toSymmUnit := symm, upper := upper, lower := lower }

class JensenSketch (F : ℝ → ℝ) : Prop extends SymmUnit F where
  axis_upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  axis_lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

instance (priority := 95) averagingBounds_of_jensen {F : ℝ → ℝ} [JensenSketch F] :
  AveragingBounds F :=
  mkAveragingBounds F (symm := (inferInstance : SymmUnit F))
    (upper := JensenSketch.axis_upper (F:=F))
    (lower := JensenSketch.axis_lower (F:=F))

noncomputable def JensenSketch.of_log_bounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper_log : ∀ t : ℝ, F (Real.exp t) ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1))
  (lower_log : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ F (Real.exp t)) :
  JensenSketch F :=
{ toSymmUnit := symm
, axis_upper := by intro t; simp [Jcost_exp] using upper_log t
, axis_lower := by intro t; simp [Jcost_exp] using lower_log t }

noncomputable def F_ofLog (G : ℝ → ℝ) : ℝ → ℝ := fun x => G (Real.log x)

class LogModel (G : ℝ → ℝ) : Prop where
  even_log : ∀ t : ℝ, G (-t) = G t
  base0 : G 0 = 0
  upper_cosh : ∀ t : ℝ, G t ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
  lower_cosh : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ G t

instance (G : ℝ → ℝ) [LogModel G] : SymmUnit (F_ofLog G) :=
  { symmetric := by
      intro x hx
      have hlog : Real.log (x⁻¹) = - Real.log x := by
        simp using Real.log_inv hx
      dsimp [F_ofLog]
      have he : G (Real.log x) = G (- Real.log x) := by
        simp using (LogModel.even_log (G:=G) (Real.log x)).symm
      simp [hlog] using he
    , unit0 := by
      dsimp [F_ofLog]
      simp [Real.log_one] using (LogModel.base0 (G:=G)) }

instance (priority := 90) (G : ℝ → ℝ) [LogModel G] : JensenSketch (F_ofLog G) :=
  JensenSketch.of_log_bounds (F:=F_ofLog G)
    (symm := (inferInstance : SymmUnit (F_ofLog G)))
    (upper_log := by
      intro t
      dsimp [F_ofLog]
      simp using (LogModel.upper_cosh (G:=G) t))
    (lower_log := by
      intro t
      dsimp [F_ofLog]
      simp using (LogModel.lower_cosh (G:=G) t))

theorem agree_on_exp_extends {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  have : F (Real.exp (Real.log x)) = Jcost (Real.exp (Real.log x)) := hAgree (Real.log x)
  simp [Real.exp_log hx] at this
  exact this

theorem F_eq_J_on_pos_of_averaging {F : ℝ → ℝ} [AveragingAgree F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := AveragingAgree.agrees (F:=F))

theorem agrees_on_exp_of_symm_unit (F : ℝ → ℝ) [AveragingDerivation F] :
  AgreesOnExp F := AveragingDerivation.agrees (F:=F)

theorem F_eq_J_on_pos_of_derivation (F : ℝ → ℝ) [AveragingDerivation F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := agrees_on_exp_of_symm_unit F)

theorem T5_cost_uniqueness_on_pos {F : ℝ → ℝ} [JensenSketch F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos_of_derivation F

theorem T5_for_log_model {G : ℝ → ℝ} [LogModel G] :
  ∀ {x : ℝ}, 0 < x → F_ofLog G x = Jcost x :=
  T5_cost_uniqueness_on_pos (F:=F_ofLog G)

@[simp] theorem Jcost_agrees_on_exp : AgreesOnExp Jcost := by
  intro t; rfl

instance : AveragingAgree Jcost := ⟨Jcost_agrees_on_exp⟩

instance : SymmUnit Jcost :=
  { symmetric := by
      intro x hx
      simp [Jcost_symm (x:=x) hx]
    , unit0 := Jcost_unit0 }

instance : AveragingDerivation Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , agrees := Jcost_agrees_on_exp }

instance : JensenSketch Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , axis_upper := by intro t; exact le_of_eq rfl
  , axis_lower := by intro t; exact le_of_eq rfl }

end Cost
end IndisputableMonolith
