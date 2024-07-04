import Lake
open Lake DSL

package «lean-lam» where
  -- add package configuration options here

lean_lib «LeanLam» where
  -- add library configuration options here

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.9.0"
/- require auto from git "https://github.com/leanprover-community/lean-auto" -/
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.9.0"


@[default_target]
lean_exe «lean-hm» where
  root := `Main
