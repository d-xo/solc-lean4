import Lean
import Std.Data.HashMap
import Init.Data.BitVec
import Mathlib.Data.Nat.Bits
import Mathlib.Computability.Encoding

open Lean Elab Meta BitVec

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
    | Syntax.ident _ _ nm _ => Name.append (.str .anonymous "Yul") nm
                            |> mkIdent
                            |> some
    | _ => none
  | _ => none

macro_rules
  -- literals
  | `(yul_literal | true) => `(doElem | pure Bool.true)
  | `(yul_literal | false) => `(doElem | pure Bool.false)
  | `(yul_literal | $n:num) => `(doElem | pure $ Word.abs $n)

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

        -- prepend the function name with yul_
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

-- Utils --

def padBuf (buf : Buf) (sz : Nat) (val : Byte) : Buf :=
  if sz <= buf.size
  then buf
  else
    let padding := Array.mkArray (sz - Array.size buf) val
    Array.append buf padding

-- NOTE: we handle the pathological case where idx + 32 overflows by just
-- reading zeros past the end. this case is actually UB according to geth, so
-- it doesn't really matter what we do here.
def readWord (buf : Buf) (idx : Word) : Word :=
  let n := BitVec.toNat idx
  let bytes : Subarray Byte :=
    { as := padBuf buf (n + 32) 0
    , start := n
    , stop := n + 32
    , h₁ := by simp
    , h₂ := by
        unfold padBuf
        · by_cases hsz : n + 32 <= buf.size
          · simp [hsz]
          · simp [hsz]
            unfold Array.size
            simp
            simp [Nat.lt_of_not_le] at hsz
            rw [←Nat.add_sub_assoc, Nat.add_sub_cancel_left]
            apply Nat.le_of_lt
            assumption
    }

  let sz_theorem : bytes.size = 32 := by unfold Subarray.size; simp
  let idx_theorem (i : Nat) : i < 32 → i < bytes.size := by
    intro h
    rw [←sz_theorem] at h
    assumption

  -- TODO: this is ugly af...
  bytes[0]'(by simp [idx_theorem])
  ++ bytes[1]'(by simp [idx_theorem])
  ++ bytes[2]'(by simp [idx_theorem])
  ++ bytes[3]'(by simp [idx_theorem])
  ++ bytes[4]'(by simp [idx_theorem])
  ++ bytes[5]'(by simp [idx_theorem])
  ++ bytes[6]'(by simp [idx_theorem])
  ++ bytes[7]'(by simp [idx_theorem])
  ++ bytes[8]'(by simp [idx_theorem])
  ++ bytes[9]'(by simp [idx_theorem])
  ++ bytes[10]'(by simp [idx_theorem])
  ++ bytes[11]'(by simp [idx_theorem])
  ++ bytes[12]'(by simp [idx_theorem])
  ++ bytes[13]'(by simp [idx_theorem])
  ++ bytes[14]'(by simp [idx_theorem])
  ++ bytes[15]'(by simp [idx_theorem])
  ++ bytes[16]'(by simp [idx_theorem])
  ++ bytes[17]'(by simp [idx_theorem])
  ++ bytes[18]'(by simp [idx_theorem])
  ++ bytes[19]'(by simp [idx_theorem])
  ++ bytes[20]'(by simp [idx_theorem])
  ++ bytes[21]'(by simp [idx_theorem])
  ++ bytes[22]'(by simp [idx_theorem])
  ++ bytes[23]'(by simp [idx_theorem])
  ++ bytes[24]'(by simp [idx_theorem])
  ++ bytes[25]'(by simp [idx_theorem])
  ++ bytes[26]'(by simp [idx_theorem])
  ++ bytes[27]'(by simp [idx_theorem])
  ++ bytes[28]'(by simp [idx_theorem])
  ++ bytes[29]'(by simp [idx_theorem])
  ++ bytes[30]'(by simp [idx_theorem])
  ++ bytes[31]'(by simp [idx_theorem])

def writeWord (buf : Buf) (idx : Word) (val : Word) : Buf :=
  sorry

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
