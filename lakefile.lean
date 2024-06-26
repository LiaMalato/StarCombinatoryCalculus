import Lake
open Lake DSL

package lean_projeto_2 where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

lean_lib «LeanProjeto2» where
  -- add library configuration options here

@[default_target]
lean_exe lean_projeto_2 where
  root := `Main
