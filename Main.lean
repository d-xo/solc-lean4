import «SolcLean4»

open Solidity
open Solidity.Add

def main : IO Unit := do

  let res := runSol $ do
    add (U256.abs 9) (U256.abs 12)

  IO.println $ "result is: " ++ repr res
