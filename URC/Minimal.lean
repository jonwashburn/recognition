import Mathlib
import IndisputableMonolith.URCAdapters.UnitsIdentity
import IndisputableMonolith.URCAdapters.EightBeat
import IndisputableMonolith.URCAdapters.ELProp
import IndisputableMonolith.URCAdapters.PhiRung

/-! Minimal URC scaffold to ensure a clean, fast build.
    This file is independent of the heavy monolith; use it for CI builds.
-/

namespace URCMinimal

def UnitsProp : Prop := IndisputableMonolith.URCAdapters.units_identity_prop
def EightBeatProp : Prop := IndisputableMonolith.URCAdapters.eightbeat_prop
def ELProp : Prop := IndisputableMonolith.URCAdapters.EL_prop
def PhiRungProp : Prop := IndisputableMonolith.URCAdapters.phi_rung_prop

structure LawfulBridge : Prop where
  units  : UnitsProp
  eight  : EightBeatProp
  el     : ELProp
  rung   : PhiRungProp

@[simp] def bridge : LawfulBridge :=
  ⟨ IndisputableMonolith.URCAdapters.units_identity_holds
  , IndisputableMonolith.URCAdapters.eightbeat_holds
  , IndisputableMonolith.URCAdapters.EL_holds
  , IndisputableMonolith.URCAdapters.phi_rung_holds ⟩

end URCMinimal
