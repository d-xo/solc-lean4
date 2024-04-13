import Aesop
import Lean
import Std.Data.HashMap
import Init.Data.Nat
import Init.Data.Nat.Lemmas
import Init.Data.BitVec
import Mathlib.Data.Nat.Bits
import Mathlib.Data.PNat.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.Computability.Encoding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Std.Data.Array.Lemmas
import «SolcLean4».Util

open Lean BitVec Vector Nat

namespace Yul

declare_syntax_cat yul_block
declare_syntax_cat yul_statement
declare_syntax_cat yul_identifier
declare_syntax_cat yul_identifier_list
declare_syntax_cat yul_expression
declare_syntax_cat yul_literal

-- Identifiers --

-- TODO: yul has different identifier rules than the built in lean parser...
syntax ident : yul_identifier
syntax "return" : yul_identifier

-- IdentifierList = Identifier ( ',' Identifier)*
syntax yul_identifier ("," yul_identifier)* : yul_identifier_list

-- Expressions --

syntax yul_identifier "(" yul_expression,* ")" : yul_expression
syntax yul_identifier : yul_expression
syntax yul_literal : yul_expression

-- Literals --
-- TODO: hex literals

syntax "true" : yul_literal
syntax "false" : yul_literal
syntax num : yul_literal
syntax str : yul_literal

-- Statements --

syntax yul_block : yul_statement
syntax ident ":=" yul_expression : yul_statement
syntax yul_expression : yul_statement

-- Blocks --

syntax "{" yul_statement* "}" : yul_block

-- Core EVM Types --

abbrev Word := BitVec 256
abbrev Addr := BitVec 160
abbrev Byte := BitVec 8
abbrev Buf := Array Byte

instance : Hashable Word where
  hash := hash ∘ BitVec.toNat

instance : Hashable Addr where
  hash := hash ∘ BitVec.toNat

-- Semantics --

syntax "assembly " yul_block : doElem

instance : Coe Syntax (TSyntax `doElem) where
  coe s := ⟨s⟩

instance : Coe (Array Syntax) (TSyntax `Lean.Parser.Term.doSeq) where
  coe s := ⟨Elab.Term.Do.mkDoSeq s⟩

-- Prepends Yul to the hierarchical name contained in the identifier
def prepend_yul : (i : TSyntax `ident) → Option (TSyntax `ident)
  | `($i:ident) => match i.raw with
    | Syntax.ident _ _ nm _
      => Name.append (.str .anonymous "Yul") nm |> mkIdent |> some
    | _ => none
  | _ => none

macro_rules
  -- literals
  | `(yul_literal | true) => `(doElem | pure Bool.true)
  | `(yul_literal | false) => `(doElem | pure Bool.false)
  | `(yul_literal | $n:num) => `(doElem | pure $n)

  -- identifiers
  | `(yul_identifier | $i:ident) => `(doElem | pure $i)

  -- blocks
  | `(doElem | assembly $b:yul_block) => expandMacros b

  | `(yul_block | { $s:yul_statement* }) => do
      let ss ← Array.mapM expandMacros s
      `(doElem | do $ss)

  -- statements
  | `(yul_statement | $i:ident := $e:yul_expression)
      => do
        let ee ← Lean.expandMacros e
        `(doElem | ($i) ← $ee)
  | `(yul_statement | $e:yul_expression)
      => do
        let ee ← Lean.expandMacros e
        `(doElem | _ ← $ee)

  -- expressions
  | `(yul_expression | $l:yul_literal) => do
      let le ← Lean.expandMacros l
      `(doElem | $le)
  | `(yul_expression | $i:yul_identifier) => do
      let ie ← Lean.expandMacros i
      `(doElem | $ie)
  -- we can't use the generic expansion below as `return` is a keyword in lean
  | `(yul_expression | return($off:yul_expression, $sz:yul_expression))
      => do
        let offe ← expandMacros off
        let sze ← expandMacros sz
        `(do
            let sz' ← $sze
            let off' ← $offe
            Yul._return off' sz'
        )
  | `(yul_expression | $i:ident( $xs:yul_expression,* ))
      => do
        -- grab only the args from the sep array
        let args := Syntax.TSepArray.getElems xs

        -- macro expand the args and generate a unique name for the result
        let exps ← Array.mapIdxM args $ λ idx arg => do
          let exp ← expandMacros arg
          let nm := idx |> .num .anonymous |> mkIdent
          let syn ← `(doElem | let $nm ← $exp)
          pure (nm, syn)

        -- prepend the function name with the Yul namespace qualifier
        match prepend_yul i with
        | some fn => do
            -- yul evaluates function args right to left, so we reverse
            let calls := Array.map Prod.snd exps |> Array.reverse

            -- call fn with the result of evaluating it's arguments
            let results := Array.map Prod.fst exps
            let info ← MonadRef.mkInfoFromRefPos
            let exec := Syntax.mkApp fn results
                     |> Syntax.node1 info `Lean.Parser.Term.doExpr

            -- squash everything together into a do block
            let seq := Array.push calls exec
            `(doElem | do $seq)
        | none => Macro.throwUnsupported


-- EVM Execution Environment --


structure CallFrame where
  adress : Addr
  memory : Buf
  calldata : Buf
  returndata : Buf
deriving Repr

instance : EmptyCollection CallFrame where
  emptyCollection := CallFrame.mk 0 #[] #[] #[]

structure VM where
  call : CallFrame
  frames : List CallFrame
  storage : Std.HashMap Addr (Std.HashMap Word Word)

-- TODO: make this not bad...
instance : Repr VM where
  reprPrec _ n := Repr.addAppParen "VM {}" n

instance : EmptyCollection VM where
  emptyCollection := VM.mk {} [] {}

inductive Result where
  | Success (vm : VM)
  | Revert (msg : Buf)
deriving Repr

abbrev EVM (a : Type) := ExceptT Result (StateM VM) a


-- readWord --


-- NOTE: we handle the pathological case where idx + 32 overflows by just
-- reading zeros past the end. this case is actually UB according to geth, so
-- it doesn't really matter what we do here.
def readWord (buf : Buf) (idx : Word) : Word :=
  let n := BitVec.toNat idx
  let bytes : Subarray Byte :=
    { as := padRight buf (n + 32) 0
    , start := n
    , stop := n + 32
    , h₁ := by simp
    , h₂ := padRight_sz_le
    }
  let res_thm : 8 * bytes.size = 256 := by
    have : bytes.size = 32 := by unfold Subarray.size; simp
    simp [this]
  BitVec.cast res_thm (BitVec.join (Subarray.toVector bytes))

def writeWord (buf : Buf) (start : Word) (val : Word) : Buf :=
  let bytes := BitVec.chunk 8 32 val
  let s := start.toNat
  -- TODO: this is a bit fucked! the buf can grow larger than u256!
  let padded := padRight buf (s + 32) 0
  Array.mapIdx buf (λ i v =>
    if s ≤ i && i < s + 32
    then bytes[i - s]'(by sorry)
    else v
  )


-- OpCodes --

def calldataload (loc : Word) : EVM Word := do
  let evm ← get
  pure $ readWord evm.call.calldata loc

def mload (loc : Word) : EVM Word := do
  let evm ← get
  pure $ readWord evm.call.memory loc

def mstore (off : Word) (val : Word) : EVM Unit := do
  let evm ← get
  set $ { evm with call.memory := writeWord evm.call.memory off val }

def add (a : Word) (b : Word) : EVM Word :=
  pure $ a + b

def mul (a : Word) (b : Word) : EVM Word :=
  pure $ a * b

def addmod (a : Word) (b : Word) (n : Word) : EVM Word :=
  pure (BitVec.ofNat 256 ((BitVec.toNat a + BitVec.toNat b) % BitVec.toNat n))

def shr (shift : Word) (val : Word) : EVM Word :=
  pure $ BitVec.ushiftRight val shift.toNat

def _return (offset : Word) (size: Word) : EVM Unit := do
  let evm ← get
  let off := offset.toNat
  let sz := size.toNat
  let mem := padRight evm.call.memory (off + sz) 0
  let data := (mem[off:off+sz]).toArray
  match evm.frames with
  | [] =>
    throw $ Result.Success { evm with call.returndata := data }
  | x::xs => do
    set $ { evm with
      call := { x with returndata := data }
      frames := xs
    }



-- Helpers --


end Yul
