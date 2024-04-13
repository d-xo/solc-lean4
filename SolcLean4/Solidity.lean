import «SolcLean4».Yul

namespace Solidity

-- The Sol monad is the same thing as the Yul monad

abbrev Sol (a : Type) := Yul.EVM a
def runSol (s : Sol a) : Except Yul.Result a
  := Prod.fst $ Id.run (StateT.run (ExceptT.run s)) {}

-- Type Classification --

-- types that have a Yul.Word as their rep
-- TODO: these should probably be monadic for consistency?
-- will we have some kinda of effect tracking in the type system?
class Value (t : Type) where
  abs : Yul.Word → t
  rep : t → Yul.Word

class Loc (t : Type) where

structure Calldata (t : Type) where
  abs ::
  rep : Yul.Word
deriving Repr

structure Memory (t : Type) where
  abs ::
  rep : Yul.Word
deriving Repr

structure Storage (t : Type) where
  abs ::
  rep : Yul.Word
deriving Repr

structure Returndata (t : Type) where
  abs ::
  rep : Yul.Word
deriving Repr

-- TODO: not sure how to implement store for this...
structure Stack (t : Type) where
  abs ::
  rep : t
deriving Repr

instance : Loc (Calldata t) where
instance : Loc (Memory t) where
instance : Loc (Storage t) where
instance : Loc (Stack t) where
instance : Loc (Returndata t) where

-- Tuples --

inductive Pair (l : Type) (r : Type) where
| Pair (x : l) (y : r) : Pair l r

-- References --

class Loadable (ref : Type) (deref : outParam Type) where
  load : ref → Sol deref
open Loadable

class Storable (ref : Type) (deref : outParam Type) where
  store : ref → deref → Sol Unit
open Storable

-- TODO: do we need this type class extension stuff in the core language?
class Ref (ref : Type) (deref : outParam Type)
  extends Storable ref deref, Loadable ref deref where

instance [Value t] : Loadable (Calldata t) t where
  load ref := do
    let rw := ref.rep
    let mut res := 0
    assembly {
      res := calldataload(rw)
    }
    return (Value.abs res)

instance [Value t] : Ref (Memory t) t where
  load ref := do
    let rw := ref.rep
    let mut res := 0
    assembly {
      res := mload(rw)
    }
    return (Value.abs res)
  store ref val := do
    let rw := ref.rep
    let vw := Value.rep val
    assembly {
      mstore(rw, vw)
    }

-- Memory Allocation --

class Alloc (t : Type) where
  new : Sol t

-- Options --

inductive Option t where
| Some (v : t) : Option t
| None : Option t
open Option

-- Containers --

-- TODO: should this return a Result?
class SetElem (cont : Type) (idx : outParam Type) (elem : outParam Type) where
  set : cont → idx → elem -> Sol Unit

class GetElem (cont : Type) (idx : outParam Type) (elem : outParam Type) where
  get : cont → idx → Sol (Option elem)

-- Addition --

class Add (t : Type) where
  add : t → t → Sol t

-- uint256 --

structure U256 where
  abs ::
  rep : Yul.Word

instance : Value U256 where
  abs := U256.abs
  rep := U256.rep

instance : Repr U256 where
  reprPrec u n := Repr.addAppParen ("U256(" ++ reprArg u.rep.toNat ++ ")") n

instance : Add U256 where
  add x y := do
    let xw := U256.rep x
    let yw := U256.rep y
    let mut zw := 0
    assembly {
      zw := add(xw, yw)
    }
    return U256.abs zw

-- byte --

structure Byte where
  abs ::
  rep : Yul.Word
deriving Repr

-- Dynamic Arrays --

-- TODO: what does it mean for this to live on the stack?
structure Vec (t : Type) where
  abs ::
  rep : Yul.Word
deriving Repr

instance : GetElem (Memory (Vec Bytes)) U256 Byte where
  get arr idx := do
    let fst := arr.rep
    let iw := idx.rep

    -- bounds check
    let mut sz := 0
    assembly { sz := mload(fst) }
    if iw ≥ sz then
      return None

    -- lookup & clean
    let mut res := 0
    assembly {
      res := mload(add(add(fst, 1), iw))
      res := shr(31, res)
    }
    return Some (Byte.abs res)


instance [Value t] : GetElem (Memory (Vec t)) U256 t where
  get arr idx := do
    let fst := arr.rep
    let iw := idx.rep

    -- bounds check
    -- TODO: should this be elems or bytes (elems for now...)
    let mut sz := 0
    assembly { sz := mload(fst) }
    if iw ≥ sz then
      return None

    -- lookup
    let mut res := 0
    assembly {
      res := mload(add(add(fst, 32),mul(iw, 32)))
    }
    return Some (Value.abs res)

instance : Alloc (Memory (Vec Byte)) where
  new := do
    let mut free := 0
    assembly {
      free := mload(64)
      mstore(64, add(free, 32))
    }
    let res := Memory.abs free
    return res


-- ABI Encoding --

class ABI (t : Type) where
  encode : t → Sol (Memory (Vec Byte))
  decode : Memory (Vec Byte) → Sol t


instance : ABI U256 where
  encode val := sorry
  decode bytes := sorry


#eval runSol $ do
  Add.add (U256.abs 9) (U256.abs 12)

end Solidity
