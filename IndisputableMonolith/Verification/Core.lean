import Mathlib
import IndisputableMonolith.Core

open Classical Function

namespace IndisputableMonolith.Verification

open Constants
open Constants.RSUnits

/-- Evidence bundle for calibration uniqueness: collects K‑gate equality and
    anchor‑invariance of both route displays for traceability. -/
structure CalibrationEvidence : Type where
  k_gate : ∀ U, BridgeEval K_A_obs U = BridgeEval K_B_obs U
  KA_invariant : ∀ {U U'} (h : UnitsRescaled U U'), BridgeEval K_A_obs U = BridgeEval K_A_obs U'
  KB_invariant : ∀ {U U'} (h : UnitsRescaled U U'), BridgeEval K_B_obs U = BridgeEval K_B_obs U'

/-- Canonical evidence derived from the global K‑gate and invariance lemmas. -/
@[simp] def calibrationEvidence_any : CalibrationEvidence :=
{ k_gate := by intro U; simp [BridgeEval, K_A_obs, K_B_obs]
, KA_invariant := by intro U U' h; exact anchor_invariance _ h
, KB_invariant := by intro U U' h; exact anchor_invariance _ h }

end IndisputableMonolith.Verification
