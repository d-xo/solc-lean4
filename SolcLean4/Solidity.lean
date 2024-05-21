import Lean
import Init.Data.BitVec
import Lean.Parser.Basic
import Init.Data.Format
import «SolcLean4».Yul

open Lean Parser Command Elab

namespace Solidity

abbrev Word := Yul.Word

-- Execution Context --


abbrev Sol (a : Type) := Yul.EVM a
def runSol (s : Sol a) : Except Yul.Result a
  := Prod.fst $ Id.run (StateT.run (ExceptT.run s)) {}


-- Syntax --

declare_syntax_cat method_decl
declare_syntax_cat type_signature
declare_syntax_cat sol_command

syntax "class" ident ":" ident ("[" ident,* "]")? "{" method_decl* "}" : sol_command
syntax ident ":" type_signature ";" : method_decl
syntax ident ("->" ident)* : type_signature

instance : Coe (Syntax) (TSyntax `term) where
  coe s := ⟨s⟩

instance : Coe (TSyntax `type_signature) (TSyntax `term) where
  coe s := ⟨s⟩

instance : Coe Syntax (TSyntax [`Lean.Parser.Command.structExplicitBinder, `Lean.Parser.Command.structImplicitBinder, `Lean.Parser.Command.structInstBinder, `Lean.Parser.Command.structSimpleBinder]) where
  coe s := ⟨s⟩

instance : Coe (Array Syntax) (TSyntaxArray [`Lean.Parser.Command.structExplicitBinder, `Lean.Parser.Command.structImplicitBinder, `Lean.Parser.Command.structInstBinder, `Lean.Parser.Command.structSimpleBinder]) where
  coe s := ⟨s.data⟩

macro_rules
  | `(type_signature | $t:ident ) => `(term | $t)
  | `(type_signature | $hd:ident -> $ret:ident ) => `(term | $hd -> $ret)
  | `(method_decl | $n:ident : $sig:type_signature ;)
      => `(structSimpleBinder | $n : $sig )

  | `(sol_command | class $clsNm : $mainArg { $methods:method_decl* })
      => do
        let ms ← Array.mapM expandMacros methods
        `(command |
          class $clsNm ($mainArg : Type) where
            mk::
            $ms*
         )

syntax "solidity {" sol_command* "}" : command
elab "solidity {" ss:sol_command* "}" : command
  => do
    _ ← Array.mapM Elab.Command.elabCommand ss
    pure ()

solidity {

class Value0 : t {
  abs : Word -> t;
  --rep : t -> Word;
}

}


-- Type Classification --


-- types that have a Yul.Word as their rep
-- TODO: these fns should probably be monadic for consistency?
class Value (t : Type) where
  abs : Yul.Word → t
  rep : t → Yul.Word


-- Booleans --


structure Bool where
  abs ::
  rep : Yul.Word
deriving Repr, BEq

instance : Coe Bool (_root_.Bool) where
  coe b := if b.rep == 1 then True else False


-- Orderings --


class Ord (t : Type) where
  eq : t → t → Sol Bool
  lt : t → t → Sol Bool
  gt : t → t → Sol Bool
  le : t → t → Sol Bool
  ge : t → t → Sol Bool
open Ord

instance : Ord Yul.Word where
  eq x y := do
    let mut res := 0
    assembly { res := eq(x, y) }
    pure (Bool.abs res)
  lt x y := do
    let mut res := 0
    assembly { res := lt(x, y) }
    pure (Bool.abs res)
  gt x y := do
    let mut res := 0
    assembly { res := gt(x, y) }
    pure (Bool.abs res)
  le x y := do
    let mut res := 0
    assembly { res := le(x, y) }
    pure (Bool.abs res)
  ge x y := do
    let mut res := 0
    assembly { res := ge(x, y) }
    pure (Bool.abs res)



-- Data Locations --


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


-- Tuples --


inductive Pair (l : Type) (r : Type) where
| Pair (x : l) (y : r) : Pair l r
deriving Repr

def Pair.fst : Solidity.Pair l r → l
| Pair x _ => x

def Pair.snd : Solidity.Pair l r → r
| Pair _ y => y


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


-- Options --


inductive Option t where
| Some (v : t) : Option t
| None : Option t
open Option


-- Lists --


-- TODO: what is the runtime representation of these things?
-- Just a bunch of yul vars after type erasure?
-- TODO: can we do some fun stuff like HLists / Vectors or does that need GADTs?
inductive List (t : Type) where
| Nil : List t
| Cons (x : t) (xs : List t)
--open List


-- Containers --


-- TODO: should this return a Result?
class SetElem (cont : Type) (idx : outParam Type) (elem : outParam Type) where
  set : cont → idx → elem -> Sol Unit

class GetElem (cont : Type) (idx : outParam Type) (elem : outParam Type) where
  get : cont → idx → Sol (Option elem)

class Expandable (cont : Type) (elem : outParam Type) where
  push : cont → elem → Sol Unit

class Joinable (cont : Type) where
  append : cont → cont → Sol cont


-- Arithmetic --


class Add (t : Type) where
  add : t → t → Sol t
open Add

instance : Add (Word) where
  add l r := do
    let mut res := 0
    assembly { res := add(l, r) }
    return res

class Mul (t : Type) where
  mul : t → t → Sol t
open Mul

instance : Mul (Word) where
  mul l r := do
    let mut res := 0
    assembly { res := mul(l, r) }
    return res

class Sub (t : Type) where
  sub : t → t → Sol t
open Sub

instance : Sub (Word) where
  sub l r := do
    let mut res := 0
    assembly { res := sub(l, r) }
    return res


-- uint256 --


structure U256 where
  abs ::
  rep : Yul.Word

instance : OfNat U256 n where
  ofNat := U256.abs n

instance : Value U256 where
  abs := U256.abs
  rep := U256.rep

instance : Repr U256 where
  reprPrec u n := Repr.addAppParen ("U256(" ++ reprArg u.rep.toNat ++ ")") n

instance : Add U256 where
  add x y := do
    let res ← Add.add x.rep y.rep
    return (U256.abs res)

instance : Ord U256 where
  eq x y := Ord.eq x.rep y.rep
  lt x y := Ord.lt x.rep y.rep
  gt x y := Ord.gt x.rep y.rep
  le x y := Ord.le x.rep y.rep
  ge x y := Ord.ge x.rep y.rep


-- Memory Allocation --


def alloc (sz : Word) : Sol Word := do
  let mut free := 0
  assembly {
    free := mload(64)
    mstore(64, add(free, sz))
  }
  return free

-- Reallocates the given area of memory.
-- * `ptr`: - The pointer to the area of memory to reallocate.
-- * `count`: - The number of bytes kept when reallocating. These are not set to 0.
-- * `newCcount`: - The number of new bytes to allocate. These are set to 0.
def realloc (ptr : Word) (count : Word) (newCount : Word) : Sol Word := do
  let noop ← Ord.le newCount count
  if noop == (Bool.abs 1)
  then pure ptr
  else do
    let newPtr ← alloc newCount
    if ← Ord.gt count 0 then
      assembly { mcopy(newPtr, ptr, count) }
    return newPtr


-- Byte --


structure Byte where
  abs ::
  rep : Yul.Word
deriving Repr


-- Dynamic Arrays --


structure Vec (t : Type) where
  abs ::
  rep : Yul.Word
deriving Repr

def Vec.mk (capacity : U256) : Sol (Memory (Vec t)) := do
  let cap := capacity.rep
  let ptr ← alloc (← add cap 2)
  assembly {
    mstore(ptr, 0)
    mstore(add(ptr,32), cap)
  }
  return Memory.abs ptr

def Vec.get (stride : Yul.Word) (fst : Yul.Word) (idx : Yul.Word) : Sol (Option Yul.Word) := do
  -- bounds check
  let mut sz := 0
  assembly { sz := mload(fst) }
  let of ← Ord.ge idx sz
  -- TODO: comparison needs sugar...
  if of == (Bool.abs 1) then
    return None

  -- lookup
  let mut res := 0
  assembly {
    -- first two slots are size & capacity
    res := mload(add(add(fst, mul(stride, 2)), mul(idx, stride)))
  }
  return Some res

instance : GetElem (Memory (Vec Bytes)) U256 Byte where
  get ptr idx := do
    match ← Vec.get 1 ptr.rep idx.rep with
    | Some r => return Some (Byte.abs r)
    | None => pure None

instance [Value t] : GetElem (Memory (Vec t)) U256 t where
  get ptr idx := do
    match ← Vec.get 32 ptr.rep idx.rep with
    | Some r => return Some (Value.abs r)
    | None => pure None

def push (stride : Word) (fst : Word) (val : Word) (store : Word → Word → Sol Unit)  := do
    -- read size and cap from slots 0 and 1
    let mut ptr := fst
    let mut sz := 0
    let mut cap := 0
    assembly {
      sz := mload(fst)
      cap := mload(add(ptr, stride))
    }

    -- resize if new size exceeds existing capacity
    let newSz ← Add.add sz stride
    if ← Ord.gt newSz cap then
      let newCap ← Mul.mul cap 2
      ptr ← realloc ptr sz newCap
      assembly { mstore(add(ptr, stride), newCap) }

    -- increment size and store new value
    assembly { mstore(ptr, newSz) }
    store sz val

instance : Expandable (Memory (Vec Byte)) Byte where
  push ptr elem := push 1 ptr.rep elem.rep $
    λ loc val => do assembly { mstore8(loc, val) }

instance [Value t] : Expandable (Memory (Vec t)) t where
  push ptr elem := push 32 ptr.rep (Value.rep elem) $
    λ loc val => do assembly { mstore(loc, val) }

instance : Joinable (Memory (Vec t)) where
  append l r := do
    let lptr := l.rep
    let mut lsz := 0
    let mut lcap := 0
    assembly {
      lsz := mload(lptr)
      lcap := mload(add(lptr,32))
    }

    let rptr := r.rep
    let mut rsz := 0
    let mut rcap := 0
    assembly {
      rsz := mload(rptr)
      rcap := mload(add(rptr,32))
    }

    let newSz ← add lsz rsz
    if ← lt newSz lcap
    then
      assembly {
        mcopy(add(lptr,lsz), rptr, rsz)
        mstore(lptr, newSz)
      }
      pure (Memory.abs lptr)
    else
      let newCap ← add lcap rcap
      let newPtr ← realloc lptr lsz newCap
      assembly {
        mstore(newPtr, newSz)
        mstore(add(newPtr, 64), newCap)
      }
      return (Memory.abs newPtr)

def Vec.drop (vec : Memory (Vec Byte)) (count : U256) : Sol Unit := do
  let ptr := vec.rep
  let cnt := count.rep
  assembly {
    -- shrink size
    -- TODO: handle underflow (needs revert?)
    let sz := mload(ptr)
    mstore(ptr, sub(sz, cnt))

    -- copy remaining elems to start
    mcopy(add(ptr, add(64, cnt)), add(ptr, 64), cnt)
  }

def Vec.size (vec : Memory (Vec t)) : Sol U256 := do
  let mut res := 0
  let ptr := vec.rep
  assembly {
    res := mload(ptr)
  }
  return (U256.abs res)

def Vec.capacity (vec : Memory (Vec t)) : Sol U256 := do
  let mut res := 0
  let ptr := vec.rep
  assembly {
    res := mload(add(ptr, 32))
  }
  return (U256.abs res)



-- ABI Encoding --
-- TODO: this is very primitive (and wrong), and only handles value types atm


class ABI (t : Type) where
  encode : t → Sol (Memory (Vec Byte))
  decode : Memory (Vec Byte) → Sol (Option t)

instance : ABI U256 where
  encode val := do
    let vec ← Vec.mk 32
    push 32 vec.rep val.rep $
      λ loc v => do assembly { mstore(loc, v) }
    return vec

  decode bytes := do
    let ptr := bytes.rep
    let mut sz := 0
    assembly { sz := mload(ptr) }
    if ← Ord.le sz 32
    then
      let mut res := 0
      assembly { res := mload(add(ptr, 64)) }
      Vec.drop bytes 32
      return Some (U256.abs res)
    else return None


instance [ABI x] [ABI y] : ABI (Pair x y) where
  encode pair := do
    let l ← ABI.encode (Pair.fst pair)
    let r ← ABI.encode (Pair.snd pair)
    Joinable.append l r
  decode bytes := do
    let l ← ABI.decode bytes
    let r ← ABI.decode bytes
    match (l, r) with
    | (Some l', Some r') => return Some (Pair.Pair l' r')
    | _ => pure None


-- Bytes4 --


structure Bytes4 where
  abs ::
  rep : Yul.Word
deriving Repr

instance : Ord Bytes4 where
  eq x y := Ord.eq x.rep y.rep
  lt x y := Ord.lt x.rep y.rep
  gt x y := Ord.gt x.rep y.rep
  le x y := Ord.le x.rep y.rep
  ge x y := Ord.ge x.rep y.rep


-- Function Dispatch --


def mkMethod [ABI a] [ABI b] [ABI c] (f : Pair a b → Sol c) : Sol Unit := do
  let mut sz := 0
  assembly { sz := calldatasize() }
  let data ← Vec.mk (U256.abs (← sub sz 4))
  match ←ABI.decode data with
  | Some as =>
      let out ← f as
      let res ← ABI.encode out
      let ptr := res.rep
      let rsz := (←Vec.size res).rep
      assembly {
        return(ptr, rsz)
      }
  -- TODO: need to implement revert
  | None => assembly { return(0,0) }


inductive Dispatch where
| Dispatch (sel : Bytes4) (impl : Sol Unit)
open Dispatch

def calldatasize : Sol U256 := do
  let mut sz := 0
  assembly { sz := calldatasize() }
  return U256.abs sz

def readSelector : Sol Bytes4 := do
  let mut res := 0
  assembly {
    res := shr(calldataload(0), 28)
  }
  return Bytes4.abs res

def callMethod (sel : Bytes4) : (methods : List Dispatch) → Sol Unit
-- TODO: implement reverts
| .Nil => do assembly { return(0,0) }
| .Cons hd tl => match hd with
  | Dispatch.Dispatch cand fn => do
    if ← eq sel cand
    then fn
    else callMethod sel tl

def mkContract (methods : List Dispatch) : Sol Unit := do
  let cdSz ← calldatasize
  if ← ge cdSz 4
  then
    -- setup free memory pointer
    assembly { mstore(64,96) }
    -- call methods
    let sel ← readSelector
    callMethod sel methods
  else
    -- TODO: implement reverts
    assembly { return(0,0) }


-- Examples --

def adder := mkContract $
  .Cons
    (Dispatch.Dispatch
      (Bytes4.abs 0x771602f7)
      (mkMethod (λ (args : Pair U256 U256) => add (Pair.fst args) (Pair.snd args)))
    )
    .Nil

def addCalldata (x : Nat) (y : Nat) : Vector Yul.Byte 68 :=
  let xd := BitVec.ofNat 256 x
  let yd := BitVec.ofNat 256 y
  let sel := BitVec.ofNat 32 0x771602f7
  BitVec.chunk 8 68 (BitVec.cast (by rfl) $ sel ++ xd ++ yd)

def setCalldata (bs : Vector Yul.Byte sz) : Sol Unit := do
  let vm ← get
  set $ { vm with call.calldata := bs.toList.toArray }

def test : Except String U256 :=
  let res := runSol $ do
    setCalldata (addCalldata 10 5)
    adder
  match res with
  | Except.error res => match res with
    | Yul.Result.Success vm =>
        let rd := vm.call.returndata
        let padded := padRight rd 32 1
        let res := BitVec.cast (by sorry) $ BitVec.join (Subarray.toVector vm.call.returndata[0:32])
        Except.ok $ U256.abs res
    | r => Except.error ∘ Std.Format.pretty $ "execution finished with an error: " ++ (repr r)
  | _ => Except.error "execution not finished"

#eval test

#eval runSol $ do
  Add.add (U256.abs 7) (U256.abs 2)


end Solidity
