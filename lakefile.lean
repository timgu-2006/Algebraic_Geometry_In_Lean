import Lake
open Lake DSL

package y2_project

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "stable"

lean_lib PolyDivision where
  globs := #[`poly_division]

@[default_target]
lean_lib PolyDivisionExec where
  globs := #[`poly_division_exec]
