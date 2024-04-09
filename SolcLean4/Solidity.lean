import «SolcLean4».Yul

namespace Solidity

-- The Sol monad is the same thing as the Yul monad

abbrev Sol a := Yul.Yul a
def emptyEVM := Yul.EVM.mk #[] #[] #[] Std.HashMap.empty
def runSol (s : Sol a) : a := Prod.fst $ Id.run (StateT.run s emptyEVM)

-- uint256 --

structure U256 where
  abs ::
  rep : Yul.Word

instance : Repr U256 where
  reprPrec u n := Repr.addAppParen ("U256(" ++ reprArg u.rep.toNat ++ ")") n

-- Addition --

class Add (t : Type) where
  add : t → t → Sol t

instance : Add U256 where
  add x y := do
    let xw := U256.rep x
    let yw := U256.rep y
    let mut zw := 0
    assembly {
      zw := add(xw, yw)
    }
    return U256.abs zw

-- References --

structure Memory (t : Type) where
  abs ::
  rep : Yul.Word
deriving Repr

structure Storage (t : Type) where
  abs ::
  rep : Yul.Word
deriving Repr

class Ref (ref : Type) (deref : Type) where
  load : ref -> Sol deref
  store : ref -> deref -> Sol Unit

instance : Ref (Memory U256) U256 where
  load ref := do
    let rw := ref.rep
    let mut res : Yul.Word := 0
    assembly {
      res := mload(rw)
    }
    return (U256.abs res)
  store ref val := do
    let rw := ref.rep
    let vw := val.rep
    assembly {
      mstore(rw, vw)
    }

#eval runSol $ do
  Add.add (U256.abs 9) (U256.abs 12)

end Solidity
