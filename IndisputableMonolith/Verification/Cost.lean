import Mathlib

namespace IndisputableMonolith
namespace Verification
namespace Cost

/-- Jensen benchmark cost on ℝ₊: J(x) = (x + x⁻¹)/2 − 1. -/
noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

structure CostRequirements (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

@[simp] lemma Jcost_unit0 : Jcost 1 = 0 := by
  simp [Jcost]

lemma Jcost_symm {x : ℝ} (hx : 0 < x) : Jcost x = Jcost x⁻¹ := by
  -- (x + x⁻¹)/2 − 1 = (x⁻¹ + (x⁻¹)⁻¹)/2 − 1 = (x⁻¹ + x)/2 − 1
  calc
    Jcost x = (x + x⁻¹) / 2 - 1 := rfl
    _       = (x⁻¹ + x) / 2 - 1 := by simp [add_comm]
    _       = (x⁻¹ + (x⁻¹)⁻¹) / 2 - 1 := by simp [inv_inv]
    _       = Jcost x⁻¹ := rfl

/-- Agreement with Jcost on the exp-axis. -/
def AgreesOnExp (F : ℝ → ℝ) : Prop := ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

@[simp] lemma Jcost_exp (t : ℝ) :
  Jcost (Real.exp t) = ((Real.exp t) + (Real.exp (-t))) / 2 - 1 := by
  -- (exp t)⁻¹ = exp (−t)
  have h : (Real.exp t)⁻¹ = Real.exp (-t) := by
    simpa [Real.exp_neg] using (Real.exp_neg t).symm
  simp [Jcost, h]

/-- Symmetry and unit normalization interface for a candidate cost. -/
class SymmUnit (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

/-- Interface: supply the averaging argument as a typeclass to obtain exp-axis agreement. -/
class AveragingAgree (F : ℝ → ℝ) : Prop where
  agrees : AgreesOnExp F

/-- Convex-averaging derivation hook: a typeclass that asserts symmetry+unit and yields exp-axis agreement. -/
class AveragingDerivation (F : ℝ → ℝ) extends SymmUnit F : Prop where
  agrees : AgreesOnExp F

lemma even_on_log_of_symm {F : ℝ → ℝ} [SymmUnit F] (t : ℝ) :
  F (Real.exp t) = F (Real.exp (-t)) := by
  have hx : 0 < Real.exp t := Real.exp_pos t
  simpa [Real.exp_neg] using (SymmUnit.symmetric (F:=F) hx)

/-- Two-sided bounds on the exp-axis against Jcost (sufficient to deduce equality there). -/
class AveragingBounds (F : ℝ → ℝ) extends SymmUnit F : Prop where
  upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

/-- From two-sided bounds on the exp-axis, conclude agreement with `Jcost`. -/
theorem agrees_on_exp_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
  AgreesOnExp F := by
  intro t
  have h₁ := AveragingBounds.upper (F:=F) t
  have h₂ := AveragingBounds.lower (F:=F) t
  exact le_antisymm_iff.mp ⟨h₁, h₂⟩

/-- From exp-axis agreement, conclude equality with Jcost on ℝ_{>0}. -/
theorem F_eq_J_on_pos (F : ℝ → ℝ)
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  refine (exists_eq_left_iff.mpr ?_).mpr rfl
  -- Choose t = log x so exp t = x
  refine ?eq
  have : Real.exp (Real.log x) = x := by simpa using Real.exp_log hx
  simpa [this] using hAgree (Real.log x)
where
  eq (x : ℝ) (hx : 0 < x) : ∃ t, Real.exp t = x := ⟨Real.log x, by simpa using Real.exp_log hx⟩

/-- Any `AveragingBounds` instance induces an `AveragingDerivation` instance. -/
instance (priority := 90) averagingDerivation_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
  AveragingDerivation F :=
  { toSymmUnit := (inferInstance : SymmUnit F)
  , agrees := agrees_on_exp_of_bounds (F:=F) }

/-- Convenience constructor to package symmetry+unit and exp-axis bounds into `AveragingBounds`. -/
def mkAveragingBounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t))
  (lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)) :
  AveragingBounds F :=
{ toSymmUnit := symm, upper := upper, lower := lower }

/-- Jensen/strict-convexity sketch: provide exp-axis bounds to obtain `AveragingBounds`. -/
class JensenSketch (F : ℝ → ℝ) extends SymmUnit F : Prop where
  axis_upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  axis_lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

instance (priority := 95) averagingBounds_of_jensen {F : ℝ → ℝ} [JensenSketch F] :
  AveragingBounds F :=
  mkAveragingBounds F (symm := (inferInstance : SymmUnit F))
    (upper := JensenSketch.axis_upper (F:=F))
    (lower := JensenSketch.axis_lower (F:=F))

/-- Build a `JensenSketch` from explicit exp-axis inequalities written with `exp`. -/
noncomputable def JensenSketch.of_log_bounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper_log : ∀ t : ℝ, F (Real.exp t) ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1))
  (lower_log : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ F (Real.exp t)) :
  JensenSketch F :=
{ toSymmUnit := symm
, axis_upper := by intro t; simpa [Jcost_exp] using upper_log t
, axis_lower := by intro t; simpa [Jcost_exp] using lower_log t }

/-- Log-axis model → positive-cost wrapper. -/
noncomputable def F_ofLog (G : ℝ → ℝ) : ℝ → ℝ := fun x => G (Real.log x)

/-- Minimal interface for log-domain models (kept light here). -/
class LogModel (G : ℝ → ℝ) : Prop where
  even_log : ∀ t : ℝ, G (-t) = G t
  base0 : G 0 = 0

end Cost
end Verification
end IndisputableMonolith
