import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.Verification.Observables

open Classical Function

namespace IndisputableMonolith.Verification

open Constants
open Constants.RSUnits

/-- Evidence bundle for calibration uniqueness: collects K‑gate equality and
    anchor‑invariance of both route displays for traceability. -/
structure CalibrationEvidence : Type where
  k_gate : ∀ U, IndisputableMonolith.BridgeEval IndisputableMonolith.K_A_obs U = IndisputableMonolith.BridgeEval IndisputableMonolith.K_B_obs U
  KA_invariant : ∀ {U U'} (h : UnitsRescaled U U'), IndisputableMonolith.BridgeEval IndisputableMonolith.K_A_obs U = IndisputableMonolith.BridgeEval IndisputableMonolith.K_A_obs U'
  KB_invariant : ∀ {U U'} (h : UnitsRescaled U U'), IndisputableMonolith.BridgeEval IndisputableMonolith.K_B_obs U = IndisputableMonolith.BridgeEval IndisputableMonolith.K_B_obs U'

/-- Canonical evidence derived from the global K‑gate and invariance lemmas. -/
@[simp] def calibrationEvidence_any : CalibrationEvidence :=
{ k_gate := IndisputableMonolith.K_gate_bridge
, KA_invariant := by intro U U' h; exact IndisputableMonolith.anchor_invariance _ h
, KB_invariant := by intro U U' h; exact IndisputableMonolith.anchor_invariance _ h }

end IndisputableMonolith.Verification
