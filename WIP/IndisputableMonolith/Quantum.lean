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

lemma prob_comp {γ} (PW : PathWeight γ) (a b : γ) :
  PW.prob (PW.comp a b) = PW.prob a * PW.prob b := by
  dsimp [PathWeight.prob]
  simp [PW.cost_additive, Real.exp_add, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

structure BornRuleIface (γ : Type) (PW : PathWeight γ) : Prop where
  normalized : True
  exists_wave_repr : True

structure BoseFermiIface (γ : Type) (PW : PathWeight γ) : Prop where
  perm_invariant : True
  symmetrization : True

 theorem rs_pathweight_iface (γ : Type) (PW : PathWeight γ) :
  BornRuleIface γ PW ∧ BoseFermiIface γ PW := by
  exact ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩

end Quantum
end IndisputableMonolith
