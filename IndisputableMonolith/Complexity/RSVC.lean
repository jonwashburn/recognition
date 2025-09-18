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

/-- RS recognizer: instance is accepted iff its Vertex Cover image has a cover. -/
def Recognizes (A : ConstraintInstance) : Prop :=
  VertexCover.HasCover (toVC A)

/-- The reduction from RS constraints to Vertex Cover (identity on fields). -/
@[simp] def reduceRS2VC : ConstraintInstance → VertexCover.Instance := toVC

/-- Correctness is immediate from the definition. -/
@[simp] theorem reduce_correct (A : ConstraintInstance) :
  Recognizes A ↔ VertexCover.HasCover (reduceRS2VC A) := Iff.rfl

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
