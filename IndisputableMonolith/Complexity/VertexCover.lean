import Mathlib

namespace IndisputableMonolith
namespace Complexity

/-- Complexity pair (functions of input size). -/
structure ComplexityPair where
  Tc : ℕ → ℕ
  Tr : ℕ → ℕ
  deriving Repr

namespace VertexCover

/-- Vertex Cover instance over `Nat` vertices. -/
structure Instance where
  vertices : List Nat
  edges    : List (Nat × Nat)
  k        : Nat
  deriving Repr

/-- A set `S` covers an edge `(u,v)` if it contains `u` or `v`. -/
def InCover (S : List Nat) (v : Nat) : Prop := v ∈ S

def EdgeCovered (S : List Nat) (e : Nat × Nat) : Prop :=
  InCover S e.fst ∨ InCover S e.snd

/-- `S` covers all edges of instance `I`. -/
def Covers (S : List Nat) (I : Instance) : Prop :=
  ∀ e, e ∈ I.edges → EdgeCovered S e

/-- There exists a vertex cover of size ≤ k. -/
def HasCover (I : Instance) : Prop :=
  ∃ S : List Nat, S.length ≤ I.k ∧ Covers S I

/-- A trivial example with no edges is always covered by the empty set. -/
def example : Instance := { vertices := [1], edges := [], k := 0 }

lemma example_hasCover : HasCover example := by
  refine ⟨[], by decide, ?_⟩
  intro e he
  cases he

lemma Covers_nil_edges (S : List Nat) (I : Instance) (h_edges : I.edges = []) : Covers S I := by
  intro e he
  simpa [Covers, h_edges] using he.elim

lemma hasCover_of_nil_edges (I : Instance) (h_edges : I.edges = []) : HasCover I := by
  refine ⟨[], by simp, ?_⟩
  intro e he
  simpa [Covers, h_edges] using he.elim

/-- Replace only the `k` field of an instance. -/
@[simp] def withK (I : Instance) (k' : Nat) : Instance := { I with k := k' }

/-- Monotonicity in `k`: if a cover of size ≤ `I.k` exists and `I.k ≤ k'`,
    then the same set witnesses a cover for `withK I k'`. -/
lemma HasCover.mono_k {I : Instance} (h : HasCover I) {k' : Nat} (hk : I.k ≤ k') :
  HasCover (withK I k') := by
  rcases h with ⟨S, hlen, hcov⟩
  refine ⟨S, Nat.le_trans hlen hk, ?_⟩
  -- Edges are unchanged by `withK`, so coverage is preserved.
  simpa [withK, Covers]

  /-! ### Monotonicity in the covering set (superset preserves coverage) -/

  lemma EdgeCovered.mono {S S' : List Nat} {e : Nat × Nat}
    (hSS' : S ⊆ S') : EdgeCovered S e → EdgeCovered S' e := by
    intro h
    rcases h with hfst | hsnd
    · exact Or.inl (hSS' hfst)
    · exact Or.inr (hSS' hsnd)

  lemma Covers.mono {S S' : List Nat} {I : Instance}
    (hSS' : S ⊆ S') (hcov : Covers S I) : Covers S' I := by
    intro e he
    have : EdgeCovered S e := hcov e he
    exact EdgeCovered.mono (S:=S) (S':=S') (e:=e) hSS' this

  /-- If `S ⊆ S'` and `S` covers `I`, then any `S'` with length ≤ `k` witnesses a cover. -/
  lemma hasCover_of_subset {I : Instance} {S S' : List Nat}
    (hcov : Covers S I) (hSS' : S ⊆ S') (hlen : S'.length ≤ I.k) : HasCover I := by
    refine ⟨S', hlen, ?_⟩
    exact Covers.mono (S:=S) (S':=S') (I:=I) hSS' hcov

end VertexCover

end Complexity

end IndisputableMonolith
