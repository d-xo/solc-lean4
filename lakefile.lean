import Lake
open Lake DSL

package «solc-lean4» where
  -- add package configuration options here

lean_lib «SolcLean4» where
  -- add library configuration options here

@[default_target]
lean_exe «solc-lean4» where
  root := `Main
