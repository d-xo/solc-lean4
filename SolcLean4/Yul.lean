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


structure EVM where
  memory : Buf
  calldata : Buf
  returndata : Buf
  storage : Std.HashMap Addr (Std.HashMap Word Word)
abbrev Yul (a : Type) : Type := StateM EVM a


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


def mload (loc : Word) : Yul Word := do
  let evm ← get
  pure $ readWord evm.memory loc

def mstore (off : Word) (val : Word) : Yul Unit := do
  let evm ← get
  set $ { evm with memory := writeWord evm.memory off val }

def add (a : Word) (b : Word) : Yul Word :=
  pure $ a + b

def addmod (a : Word) (b : Word) (n : Word) : Yul Word :=
  pure (BitVec.ofNat 256 ((BitVec.toNat a + BitVec.toNat b) % BitVec.toNat n))


-- Helpers --


end Yul
