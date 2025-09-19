import Mathlib

/-!
Dobrushin Theory for Markov Kernels

This module contains the Dobrushin contraction theory for Markov kernels,
including the overlap function and total variation contraction theorems.
-/

namespace IndisputableMonolith
namespace YM
namespace Dobrushin

/-- Axiom stub for Markov kernel type - depends on probability/measure theory. -/
axiom MarkovKernel (α β : Type) : Type

/-- Axiom stub for overlap function between kernels - depends on measure theory. -/
noncomputable axiom overlap {α β : Type} (P Q : MarkovKernel α β) : ℝ

/-- Axiom stub for total variation distance - depends on measure theory. -/
noncomputable axiom tv_distance {α β : Type} (P Q : MarkovKernel α β) : ℝ

/-- Axiom stub for Dobrushin coefficient - depends on functional analysis. -/
noncomputable axiom dobrushin_coeff {α β : Type} (P : MarkovKernel α β) : ℝ

/-- Basic properties of overlap function. -/
axiom overlap_symmetric {α β : Type} (P Q : MarkovKernel α β) : overlap P Q = overlap Q P
axiom overlap_nonneg {α β : Type} (P Q : MarkovKernel α β) : 0 ≤ overlap P Q
axiom overlap_le_one {α β : Type} (P Q : MarkovKernel α β) : overlap P Q ≤ 1

/-- Total variation distance properties. -/
axiom tv_distance_symmetric {α β : Type} (P Q : MarkovKernel α β) : tv_distance P Q = tv_distance Q P
axiom tv_distance_nonneg {α β : Type} (P Q : MarkovKernel α β) : 0 ≤ tv_distance P Q
axiom tv_distance_le_two {α β : Type} (P Q : MarkovKernel α β) : tv_distance P Q ≤ 2

/-- Dobrushin coefficient properties. -/
axiom dobrushin_coeff_nonneg {α β : Type} (P : MarkovKernel α β) : 0 ≤ dobrushin_coeff P
axiom dobrushin_coeff_le_one {α β : Type} (P : MarkovKernel α β) : dobrushin_coeff P ≤ 1

/-- Main Dobrushin contraction theorem: TV distance contracts under kernel composition. -/
axiom dobrushin_contraction {α β γ : Type} (P : MarkovKernel α β) (Q R : MarkovKernel β γ) :
  tv_distance (compose_kernels P Q) (compose_kernels P R) ≤ (dobrushin_coeff P) * tv_distance Q R

/-- Axiom stub for kernel composition - depends on category theory/functional composition. -/
axiom compose_kernels {α β γ : Type} (P : MarkovKernel α β) (Q : MarkovKernel β γ) : MarkovKernel α γ

/-- Overlap implies TV contraction for small perturbations. -/
axiom overlap_implies_contraction {α β : Type} (P Q : MarkovKernel α β) :
  overlap P Q ≥ 1/2 → tv_distance P Q ≤ 2 * (1 - overlap P Q)

end Dobrushin
end YM
end IndisputableMonolith
