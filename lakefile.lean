import Lake
open Lake DSL

package «lean-lam» where
  -- add package configuration options here

lean_lib «LeanLam» where
  -- add library configuration options here

require std from git "https://github.com/leanprover/std4" @ "v4.4.0"


@[default_target]
lean_exe «lean-hm» where
  root := `Main
