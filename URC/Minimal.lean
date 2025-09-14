import Mathlib

/-! Minimal URC scaffold to ensure a clean, fast build.
    This file is independent of the heavy monolith; use it for CI builds.
-/

namespace URCMinimal

def UnitsProp : Prop := True
def EightBeatProp : Prop := True
def ELProp : Prop := True
def PhiRungProp : Prop := True

structure LawfulBridge : Prop where
  units  : UnitsProp
  eight  : EightBeatProp
  el     : ELProp
  rung   : PhiRungProp

@[simp] def bridge : LawfulBridge := ⟨True.intro, True.intro, True.intro, True.intro⟩

@[simp] def ok : True := True.intro

end URCMinimal
