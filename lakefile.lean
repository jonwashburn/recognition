import Lake
open Lake DSL

package recognition

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib IndisputableMonolith

lean_exe ci_checks {
  root := `CI.Checks
}
