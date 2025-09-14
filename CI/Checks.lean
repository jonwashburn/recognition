import IndisputableMonolith

-- Compile-time checks for Route A/B symbols
#check IndisputableMonolith.URCAdapters.routeA_end_to_end_demo
#check IndisputableMonolith.URCAdapters.routeB_closure_report
#check IndisputableMonolith.URCAdapters.grand_manifest
#check IndisputableMonolith.URC.BridgeAxioms.bridge_inevitability
#check IndisputableMonolith.URCGenerators.determination_by_generators

-- Also reference the concrete Manifest bridge to ensure it elaborates
#check IndisputableMonolith.URC.BridgeAxioms.Manifest.bridge

def main : IO Unit := do
  let a := IndisputableMonolith.URCAdapters.routeA_end_to_end_demo
  let b := IndisputableMonolith.URCAdapters.routeB_closure_report
  let ab := IndisputableMonolith.URCAdapters.grand_manifest
  IO.println s!"Route A: {a}"
  IO.println s!"Route B: {b}"
  IO.println s!"AB: {ab}"
