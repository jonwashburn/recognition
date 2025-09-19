import Mathlib

namespace IndisputableMonolith
namespace YM

noncomputable section
open Classical Complex

/-- Finite-dimensional transfer kernel acting on functions `ι → ℂ`. -/
structure TransferKernel (ι : Type) where
  T : (ι → ℂ) →L[ℂ] (ι → ℂ)

/-- Finite matrix view over an index set `ι`. Uses complex entries for direct linearization. -/
structure MatrixView (ι : Type) [Fintype ι] [DecidableEq ι] where
  A : Matrix ι ι ℂ

/-- Promote a linear map to a continuous linear map on function spaces. -/
noncomputable def CLM.ofLM {ι : Type}
  (L : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
{ toLinearMap := L, cont := by exact ContinuousLinearMap.continuous _ }

/-- A bridge witnessing that kernel `K.T` equals the linear map induced by the matrix `V.A`. -/
structure MatrixBridge (ι : Type) [Fintype ι] [DecidableEq ι]
  (K : TransferKernel ι) (V : MatrixView ι) where
  intertwine : K.T = CLM.ofLM (Matrix.toLin' V.A)

/-- Prop-level: kernel `K` has a concrete finite matrix view `V`. -/
def KernelHasMatrixView (ι : Type) [Fintype ι] [DecidableEq ι]
  (K : TransferKernel ι) (V : MatrixView ι) : Prop :=
  Nonempty (MatrixBridge ι K V)

/-- Build a concrete kernel from a matrix view, with a definitive bridge. -/
noncomputable def buildKernelFromMatrix (ι : Type) [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) : Σ K : TransferKernel ι, MatrixBridge ι K V :=
by
  let K : TransferKernel ι := { T := CLM.ofLM (Matrix.toLin' V.A) }
  exact ⟨K, { intertwine := rfl }⟩

/-- Canonical strictly-positive row-stochastic 3×3 kernel example (constant 1/3 entries),
    realized as a matrix-intertwined transfer kernel on `Fin 3`. -/
noncomputable def constantStochastic3x3 : MatrixView (Fin 3) :=
{ A := fun _ _ => ((1/3 : ℝ) : ℂ) }

noncomputable def kernel3x3_with_bridge :
  Σ K : TransferKernel (Fin 3), MatrixBridge (Fin 3) K constantStochastic3x3 :=
  buildKernelFromMatrix (ι := Fin 3) constantStochastic3x3

end
end YM
end IndisputableMonolith
