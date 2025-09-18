import URC.Minimal

/-!
  Minimal CI smoke check: keep this fast and independent from the heavy monolith.
  This executable is only to verify the toolchain runs in CI.
-/

def main : IO Unit := do
  let _ := URCMinimal.bridge
  IO.println "CI smoke: toolchain OK, minimal URC intact."
