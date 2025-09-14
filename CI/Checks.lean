/-!
  Minimal CI smoke check: keep this fast and independent from the heavy monolith.
  This executable is only to verify the toolchain runs in CI.
-/

def main : IO Unit := do
  IO.println "CI smoke: toolchain OK, lake exe ran."
