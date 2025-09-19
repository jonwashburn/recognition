import Mathlib
import IndisputableMonolith.Constants
-- Avoid importing heavier DEC modules; we provide a local minimal skeleton below.

namespace IndisputableMonolith
namespace TruthCore

/-! Dependency-light exports from the monolith tail: DEC wrappers and a display identity. -/

open Constants

/-! Local minimal DEC skeleton (avoid importing heavier modules). -/
namespace DEC

universe u

structure CochainSpace (A : Type u) [Zero A] where
  d0 : A → A
  d1 : A → A
  d2 : A → A
  dd01 : ∀ x, d1 (d0 x) = 0
  dd12 : ∀ x, d2 (d1 x) = 0

namespace CochainSpace

variable {A : Type u} [Zero A]

def F (X : CochainSpace A) (A1 : A) : A := X.d1 A1

theorem bianchi (X : CochainSpace A) (A1 : A) : X.d2 (X.F A1) = 0 := by
  unfold F
  simpa using X.dd12 A1

end CochainSpace
end DEC

/-! ### DEC wrappers (typed against the existing DEC skeleton) -/

namespace DECExports

variable {A : Type} [Zero A]

/-- dd=0 exporter: both successive coboundaries vanish. -/
theorem dec_dd_eq_zero (X : DEC.CochainSpace A) :
  (∀ a, X.d1 (X.d0 a) = 0) ∧ (∀ b, X.d2 (X.d1 b) = 0) := by
  exact ⟨(by intro a; simpa using X.dd01 a), (by intro b; simpa using X.dd12 b)⟩

/-- Bianchi exporter: dF = 0. -/
theorem dec_bianchi (X : DEC.CochainSpace A) (A1 : A) :
  X.d2 (X.F A1) = 0 := by
  simpa using DEC.CochainSpace.bianchi X A1

end DECExports

/-! ### Display identity (dimensionless speed ratio) -/

end TruthCore
end IndisputableMonolith

/-- Local WIP declarations for displays (keep it minimal and axiomatized). -/
namespace IndisputableMonolith
namespace Constants

@[simp] noncomputable def RSUnits.tau_rec_display (U : RSUnits) : ℝ := K * U.tau0
@[simp] noncomputable def RSUnits.lambda_kin_display (U : RSUnits) : ℝ := K * U.ell0
axiom RSUnits.display_speed_eq_c (U : RSUnits) :
  (RSUnits.lambda_kin_display U) / (RSUnits.tau_rec_display U) = U.c

end Constants
end IndisputableMonolith

namespace IndisputableMonolith
namespace TruthCore

/-- Alias: time-kernel ratio is dimensionless (invariant under common rescaling). -/
theorem display_speed_identity (U : IndisputableMonolith.Constants.RSUnits) :
  (IndisputableMonolith.Constants.RSUnits.lambda_kin_display U)
    / (IndisputableMonolith.Constants.RSUnits.tau_rec_display U) = U.c :=
  IndisputableMonolith.Constants.RSUnits.display_speed_eq_c U

end TruthCore
end IndisputableMonolith


