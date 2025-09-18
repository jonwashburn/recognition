import Mathlib

namespace IndisputableMonolith
namespace Bridge
namespace Masses

/-- Gauge equivalence on masses: identify up to a nonzero scaling factor. -/
def GaugeEq (m₁ m₂ : ℝ) : Prop := ∃ c : ℝ, c ≠ 0 ∧ m₁ = c * m₂

@[simp] lemma gauge_refl (m : ℝ) : GaugeEq m m := ⟨1, by norm_num, by simp⟩

@[simp] lemma gauge_symm {a b : ℝ} : GaugeEq a b → GaugeEq b a := by
  intro h; rcases h with ⟨c, hc, h⟩
  refine ⟨1/c, one_div_ne_zero hc, ?_⟩
  -- a = c*b ⇒ b = (1/c)*a
  have : a = (1/c) * b := by
    have := congrArg (fun x => (1/c) * x) h
    -- (1/c)*(c*b) = b
    simpa [mul_comm, mul_left_comm, mul_assoc, inv_mul_cancel hc] using this.symm
  simpa [this, mul_comm]

@[simp] lemma gauge_trans {a b c : ℝ} : GaugeEq a b → GaugeEq b c → GaugeEq a c := by
  intro h₁ h₂; rcases h₁ with ⟨x, hx, hxEq⟩; rcases h₂ with ⟨y, hy, hyEq⟩
  refine ⟨x*y, mul_ne_zero hx hy, ?_⟩
  simpa [hxEq, hyEq, mul_comm, mul_left_comm, mul_assoc]

end Masses
end Bridge
end IndisputableMonolith
