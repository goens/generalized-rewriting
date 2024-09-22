import Lake
open Lake DSL

package «GeneralizedRewriting» where
  -- add package configuration options here

lean_lib «GeneralizedRewriting» where
  -- add library configuration options here

@[default_target]
lean_exe «generalizedrewriting» where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "main"
