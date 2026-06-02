import Lake
open Lake DSL

package y2_project

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "stable"

lean_lib PolyDivision where
  globs := #[`poly_division]

lean_lib PolyDivisionExec where
  globs := #[`poly_division_exec]

lean_lib AffineVarieties where
  globs := #[`affine_varieties]

lean_lib Elimination where
  globs := #[`elimination]

@[default_target]
lean_lib ProjectiveVarieties where
  globs := #[`projective_varieties]
