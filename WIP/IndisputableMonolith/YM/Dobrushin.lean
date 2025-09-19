import Mathlib

namespace IndisputableMonolith
namespace YM
namespace Dobrushin

open scoped BigOperators

variable {ι : Type} [Fintype ι]

/-- Minimal Markov kernel interface for overlap computations. -/
structure MarkovKernel (ι : Type) [Fintype ι] where
  P : ι → ι → ℝ
  nonneg : ∀ i j, 0 ≤ P i j
  rowSum_one : ∀ i, ∑ j, P i j = 1

@[simp] def row (K : MarkovKernel ι) (i : ι) : ι → ℝ := fun j => K.P i j

/-- Row–row overlap `∑j min(P i j, P i' j)` in [0,1]. -/
def overlap (K : MarkovKernel ι) (i i' : ι) : ℝ := ∑ j, min (K.P i j) (K.P i' j)

lemma overlap_nonneg (K : MarkovKernel ι) (i i' : ι) : 0 ≤ overlap K i i' := by
  classical
  refine Finset.sum_nonneg ?_
  intro j _; exact min_nonneg (K.nonneg i j) (K.nonneg i' j)

lemma overlap_le_one (K : MarkovKernel ι) (i i' : ι) : overlap K i i' ≤ 1 := by
  classical
  have hle : ∀ j, min (K.P i j) (K.P i' j) ≤ K.P i j := by intro j; exact min_le_left _ _
  have := Finset.sum_le_sum (fun j _ => hle j)
  simpa [overlap, K.rowSum_one i]

/-- TV contraction certificate from uniform overlap lower bound β ∈ (0,1]. -/
def TVContractionMarkov (K : MarkovKernel ι) (α : ℝ) : Prop := (0 ≤ α) ∧ (α < 1)

theorem tv_contraction_from_overlap_lb (K : MarkovKernel ι) {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hβ : ∀ i i', β ≤ overlap K i i') : TVContractionMarkov K (α := 1 - β) := by
  constructor <;> linarith

end Dobrushin
end YM
end IndisputableMonolith
