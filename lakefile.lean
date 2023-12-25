import Lake
open Lake DSL

package «lean-hm» where
  -- add package configuration options here

lean_lib «LeanHm» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-hm» where
  root := `Main
