import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "v4.7.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.7.0"

package «solc-lean4» where
  -- add package configuration options here

lean_lib «SolcLean4» where
  -- add library configuration options here

@[default_target]
lean_exe «solc-lean4» where
  root := `Main
