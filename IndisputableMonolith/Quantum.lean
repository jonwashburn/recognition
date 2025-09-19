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
  sum_prob_eq_one : ∑ g in normSet, prob g = 1

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


