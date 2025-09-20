import Mathlib

namespace IndisputableMonolith
namespace Quantum

open scoped BigOperators

structure PathWeight (γ : Type) where
  C : γ → ℝ
  comp : γ → γ → γ
  cost_additive : ∀ a b, C (comp a b) = C a + C b
  prob : γ → ℝ := fun g => Real.exp (-(C g))
  normSet : Finset γ
  sum_prob_eq_one : Finset.sum normSet (fun g => prob g) = 1
-- (prob_comp omitted in WIP minimal stub)

structure BornRuleIface (γ : Type) (PW : PathWeight γ) : Prop where
  normalized : Finset.sum PW.normSet (fun g => PW.prob g) = 1
  prob_nonneg : ∀ g, 0 ≤ PW.prob g

structure BoseFermiIface (γ : Type) (PW : PathWeight γ) : Prop where
  prob_comp_mul : ∀ a b, PW.prob (PW.comp a b) = PW.prob a * PW.prob b
  prob_mul_comm : ∀ a b, PW.prob a * PW.prob b = PW.prob b * PW.prob a

theorem rs_pathweight_iface (γ : Type) (PW : PathWeight γ) :
  BornRuleIface γ PW ∧ BoseFermiIface γ PW := by
  constructor
  · refine ⟨?hnorm, ?hnonneg⟩
    · simpa using PW.sum_prob_eq_one
    · intro g; have : 0 ≤ Real.exp (-(PW.C g)) := by exact Real.exp_nonneg _
      simpa [PathWeight.prob] using this
  · refine ⟨?hcomp, ?hcomm⟩
    · intro a b
      -- exp(−(C a + C b)) = exp(−C a) * exp(−C b)
      have hadd : PW.C (PW.comp a b) = PW.C a + PW.C b := PW.cost_additive a b
      have : Real.exp (-(PW.C a + PW.C b)) = Real.exp (-(PW.C a)) * Real.exp (-(PW.C b)) := by
        have : -(PW.C a + PW.C b) = -(PW.C a) + -(PW.C b) := by simp [neg_add]
        simpa [this, Real.exp_add]
      simpa [PathWeight.prob, hadd] using this
    · intro a b; simpa [mul_comm]

end Quantum
end IndisputableMonolith
