import Mathlib

namespace IndisputableMonolith
namespace Patterns

open Classical

@[simp] def Pattern (d : Nat) := (Fin d → Bool)

@[simp] lemma card_pattern (d : Nat) : Fintype.card (Pattern d) = 2 ^ d := by
  classical
  simpa [Pattern, Fintype.card_bool, Fintype.card_fin] using
    (Fintype.card_fun (Fin d) Bool)

lemma card_pattern_pos (d : Nat) : 0 < Fintype.card (Pattern d) := by
  classical
  have : 0 < (2 : Nat) ^ d := by exact pow_pos (by decide : 0 < 2) d
  simpa [card_pattern d]

@[simp] lemma card_pattern_succ (d : Nat) :
  Fintype.card (Pattern (d+1)) = 2 * Fintype.card (Pattern d) := by
  classical
  simp [card_pattern (d+1), card_pattern d, pow_succ, Nat.mul_comm]

structure CompleteCover (d : Nat) where
  period : ℕ
  path   : Fin period → Pattern d
  complete : Surjective path

/-- There exists a complete cover of exact length `2^d` for d‑dimensional patterns. -/
 theorem cover_exact_pow (d : Nat) : ∃ w : CompleteCover d, w.period = 2 ^ d := by
  classical
  let e := (Fintype.equivFin (Pattern d)).symm
  refine ⟨{ period := Fintype.card (Pattern d)
          , path := fun i => e i
          , complete := (Fintype.equivFin (Pattern d)).symm.surjective }, ?_⟩
  simpa [card_pattern d]

/-- There exists an 8‑tick complete cover for 3‑bit patterns. -/
 theorem period_exactly_8 : ∃ w : CompleteCover 3, w.period = 8 := by
  simpa using cover_exact_pow 3

/‑‑ ## T6 alias theorems -/
 theorem T6_exist_exact_2pow (d : Nat) : ∃ w : CompleteCover d, w.period = 2 ^ d :=
  cover_exact_pow d

 theorem T6_exist_8 : ∃ w : CompleteCover 3, w.period = 8 :=
  period_exactly_8

/-- For any dimension `d`, the exact cover of period `2^d` has positive period. -/
 theorem T6_exist_exact_pos (d : Nat) : ∃ w : CompleteCover d, 0 < w.period := by
  obtain ⟨w, hp⟩ := cover_exact_pow d
  have : 0 < (2 : ℕ) ^ d := by
    exact pow_pos (by decide : 0 < (2 : ℕ)) d
  exact ⟨w, by simpa [hp] using this⟩

/-- The 3‑bit complete cover of period 8 has positive period. -/
 theorem period_exactly_8_pos : ∃ w : CompleteCover 3, 0 < w.period := by
  obtain ⟨w, hp⟩ := period_exactly_8
  have : 0 < (8 : ℕ) := by decide
  exact ⟨w, by simpa [hp] using this⟩

end Patterns
end IndisputableMonolith
