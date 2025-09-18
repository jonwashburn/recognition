import Mathlib

namespace IndisputableMonolith
namespace Complexity
namespace BalancedParityHidden

variable {n : ℕ} [DecidableEq (Fin n)]

/-- Hidden mask encoder: bit b with mask R is `R` if b=false and `bnot ∘ R` if b=true. -/
def enc (b : Bool) (R : Fin n → Bool) : Fin n → Bool :=
  fun i => if b then bnot (R i) else R i

@[simp] lemma enc_false (R : Fin n → Bool) : enc (n:=n) false R = R := by
  funext i; simp [enc]

@[simp] lemma enc_true (R : Fin n → Bool) : enc (n:=n) true R = (fun i => bnot (R i)) := by
  funext i; simp [enc]

/-- Restrict a full word to a queried index set `M`. -/
def restrict (f : Fin n → Bool) (M : Finset (Fin n)) : {i // i ∈ M} → Bool :=
  fun i => f i.val

@[simp] lemma restrict_enc_false (R : Fin n → Bool) (M : Finset (Fin n)) :
  restrict (n:=n) (enc false R) M = restrict (n:=n) R M := by
  funext i; simp [restrict, enc]

@[simp] lemma restrict_enc_true (R : Fin n → Bool) (M : Finset (Fin n)) :
  restrict (n:=n) (enc true R) M = (fun i => bnot (restrict (n:=n) R M i)) := by
  funext i; simp [restrict, enc]

/-- Extend a partial assignment on `M` to a full mask by defaulting to `false` off `M`. -/
def extendMask (a : {i // i ∈ M} → Bool) (M : Finset (Fin n)) : Fin n → Bool :=
  fun i => if h : i ∈ M then a ⟨i, h⟩ else false

@[simp] lemma extendMask_in (a : {i // i ∈ M} → Bool) {i : Fin n} (h : i ∈ M) :
  extendMask (n:=n) a M i = a ⟨i, h⟩ := by
  simp [extendMask, h]

@[simp] lemma extendMask_notin (a : {i // i ∈ M} → Bool) {i : Fin n} (h : i ∉ M) :
  extendMask (n:=n) a M i = false := by
  simp [extendMask, h]

@[simp] lemma restrict_extendMask (a : {i // i ∈ M} → Bool) (M : Finset (Fin n)) :
  restrict (n:=n) (extendMask (n:=n) a M) M = a := by
  funext i
  simp [restrict, extendMask]

/-- Any fixed-view decoder on a set `M` of queried indices can be fooled by a suitable `(b,R)`. -/
 theorem adversarial_failure (M : Finset (Fin n))
  (g : (({i // i ∈ M} → Bool)) → Bool) :
  ∃ (b : Bool) (R : Fin n → Bool),
    g (restrict (n:=n) (enc b R) M) ≠ b := by
  classical
  -- Pick an arbitrary local view `a` and force the decoder to predict `b' := g a`.
  let a : {i // i ∈ M} → Bool := fun _ => false
  let b' : Bool := g a
  -- Choose the true bit to be the opposite of the decoder's prediction.
  let b : Bool := bnot b'
  -- Choose the mask so that the restricted encoding equals `a`.
  let R : Fin n → Bool :=
    if b = false then extendMask a M else extendMask (fun i => bnot (a i)) M
  have hRestr : restrict (n:=n) (enc b R) M = a := by
    funext i
    dsimp [restrict, enc, R, extendMask]
    by_cases hbf : b = false
    · -- Then `R = extendMask a M`, and restriction is exactly `a` on `M`.
      simp [hbf, dif_pos i.property]
    · have hb : b = true := by cases b <;> simp_all
      -- Then `R = extendMask (bnot ∘ a) M`, and restriction cancels the bnot.
      simp [hb, dif_pos i.property]
  refine ⟨b, R, ?_⟩
  -- The decoder outputs `g a = b' = bnot b`, hence it is wrong.
  have : g (restrict (n:=n) (enc b R) M) = b' := by simpa [hRestr]
  have hbrel : b = bnot b' := rfl
  cases b <;> simp [hbrel, this]

/-- If a decoder is correct for all `(b,R)` while querying only `M`, contradiction. -/
 theorem no_universal_decoder (M : Finset (Fin n))
  (g : (({i // i ∈ M} → Bool)) → Bool) :
  ¬ (∀ (b : Bool) (R : Fin n → Bool), g (restrict (n:=n) (enc b R) M) = b) := by
  classical
  intro h
  rcases adversarial_failure (n:=n) M g with ⟨b, R, hw⟩
  have := h b R
  exact hw this

/-- Query lower bound (worst-case, adversarial): any universally-correct decoder
    must inspect all `n` indices. -/
theorem omega_n_queries
  (M : Finset (Fin n)) (g : (({i // i ∈ M} → Bool)) → Bool)
  (hMlt : M.card < n) :
  ¬ (∀ (b : Bool) (R : Fin n → Bool), g (restrict (n:=n) (enc b R) M) = b) :=
  no_universal_decoder (n:=n) M g

end BalancedParityHidden
end Complexity
end IndisputableMonolith
