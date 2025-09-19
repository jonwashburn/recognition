import Mathlib
import IndisputableMonolith.Verification
-- Keep deps minimal; use base Verification scaffold only.

namespace IndisputableMonolith
namespace Verification

/-- Rendered falsifiability item tying a failure condition to a guarding lemma. -/
structure Falsifiable where
  id          : String
  wouldFailIf : String
  guardedBy   : String
deriving Repr

/-- List of falsifiability conditions with guarding lemmas. -/
@[simp] def falsifiabilityRendered : List Falsifiable :=
  [ { id := "KGateMismatch"
    , wouldFailIf := "K_A ≠ K_B"
    , guardedBy := "Verification.K_gate_bridge"
    }
  , { id := "ConeViolation"
    , wouldFailIf := "∃ n x y, rad y − rad x > c · (time y − time x)"
    , guardedBy := "Verification.cone_bound_export"
    }
  ]

/-- Machine-readable manifest: claims, gates, and knobs count. -/
structure RenderedManifest where
  claims         : List RenderedClaim
  gates          : List GateSpec
  falsifiability : List Falsifiable
  knobs          : Nat
deriving Repr

@[simp] def claimIds : List String := dimlessClaimsRendered.map (fun c => c.id)
@[simp] def gateIds  : List String := gatesRendered.map (fun g => g.id)

@[simp] def manifest : RenderedManifest :=
{ claims := dimlessClaimsRendered
, gates  := gatesRendered
, falsifiability := falsifiabilityRendered
, knobs  := knobsCount }

@[simp] def manifestStrings : List String :=
  [ "claims={" ++ String.intercalate ", " claimIds ++ "}"
  , "gates={"  ++ String.intercalate ", " gateIds  ++ "}"
  , "knobs="    ++ toString knobsCount ]

end Verification
end IndisputableMonolith


