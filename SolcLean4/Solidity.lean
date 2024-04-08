import «SolcLean4».Yul

namespace Solidity

-- The Sol monad is the same thing as the Yul monad

abbrev Sol a := Yul.Yul a
def emptyEVM := Yul.EVM.mk [] [] [] Std.HashMap.empty
def runSol (s : Sol a) : a := Prod.fst $ Id.run (StateT.run s emptyEVM)

-- uint256 --

structure U256 where
  abs ::
  rep : Yul.Word
deriving Repr

-- Addition --

class Add (t : Type) where
  add : t → t → Sol t

instance : Add U256 where
  add x y := do
    let xw := U256.rep x
    let yw := U256.rep y
    let mut zw := 0
    /-
      this expands to:

      do
        let y' ← pure yw
        let x' ← pure xw
        zw ← yul_add x' y'
    -/
    assembly {
      zw := add(xw, yw)
    }
    return U256.abs zw

#eval runSol $ do
  Add.add (U256.abs 9) (U256.abs 12)

end Solidity
