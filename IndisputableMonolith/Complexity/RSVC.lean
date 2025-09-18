import Mathlib
import IndisputableMonolith.Complexity.VertexCover

namespace IndisputableMonolith
namespace Complexity

namespace RSVC

/-- RS constraint instance mapped to edges to be covered. -/
structure ConstraintInstance where
  vertices    : List Nat
  constraints : List (Nat × Nat)
  k           : Nat
  deriving Repr

/-- Forgetful map to a Vertex Cover instance. -/
@[simp] def toVC (A : ConstraintInstance) : VertexCover.Instance :=
{ vertices := A.vertices, edges := A.constraints, k := A.k }

/-- Replace only the `k` field of an RS constraint instance. -/
@[simp] def withK (A : ConstraintInstance) (k' : Nat) : ConstraintInstance := { A with k := k' }

@[simp] lemma toVC_withK (A : ConstraintInstance) (k' : Nat) :
  toVC (withK A k') = VertexCover.withK (toVC A) k' := rfl

@[simp] lemma toVC_vertices (A : ConstraintInstance) :
  (toVC A).vertices = A.vertices := rfl

@[simp] lemma toVC_edges (A : ConstraintInstance) :
  (toVC A).edges = A.constraints := rfl

@[simp] lemma toVC_k (A : ConstraintInstance) :
  (toVC A).k = A.k := rfl

/-- RS recognizer: instance is accepted iff its Vertex Cover image has a cover. -/
def Recognizes (A : ConstraintInstance) : Prop :=
  VertexCover.HasCover (toVC A)

/-- The reduction from RS constraints to Vertex Cover (identity on fields). -/
@[simp] def reduceRS2VC : ConstraintInstance → VertexCover.Instance := toVC

/-- Correctness is immediate from the definition. -/
@[simp] theorem reduce_correct (A : ConstraintInstance) :
  Recognizes A ↔ VertexCover.HasCover (reduceRS2VC A) := Iff.rfl

/-- Trivial acceptance if there are no constraints (empty edge set). -/
@[simp] lemma Recognizes_of_nil_constraints (A : ConstraintInstance)
  (h : A.constraints = []) : Recognizes A := by
  dsimp [Recognizes]
  have : (toVC A).edges = [] := by simpa [toVC_edges] using h
  exact VertexCover.hasCover_of_nil_edges (I := toVC A) this

/-- Monotonicity in `k`: recognition is preserved if we increase `k`. -/
lemma Recognizes.mono_k {A : ConstraintInstance} (h : Recognizes A)
  {k' : Nat} (hk : A.k ≤ k') : Recognizes (withK A k') := by
  dsimp [Recognizes] at h ⊢
  -- Transfer to VertexCover via `toVC` and reuse its monotonicity.
  simpa [toVC_withK] using (VertexCover.HasCover.mono_k (I := toVC A) h hk)

/-- RS‑preserving reduction scaffold: relates complexities up to monotone envelopes. -/
structure RSPreserving (A B : Type) where
  sizeA : A → ℕ
  sizeB : B → ℕ
  reduce : A → B
  TcBound : (ℕ → ℕ) → Prop := fun _ => True
  TrBound : (ℕ → ℕ) → Prop := fun _ => True
  deriving Repr

/-- RS‑preserving wrapper bundling sizes and the reduction map. -/
def rs_preserving_RS2VC : RSPreserving ConstraintInstance VertexCover.Instance :=
{ sizeA := fun a => a.vertices.length + a.constraints.length
, sizeB := fun b => b.vertices.length + b.edges.length
, reduce := reduceRS2VC }

end RSVC

end Complexity

end IndisputableMonolith
