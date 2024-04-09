import Aesop
import Lean
import Std.Data.HashMap
import Init.Data.Nat
import Init.Data.BitVec
import Mathlib.Data.Nat.Bits
import Mathlib.Computability.Encoding
import Std.Data.Array.Lemmas

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
    | Syntax.ident _ _ nm _
      => Name.append (.str .anonymous "Yul") nm |> mkIdent |> some
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


---------------------------------------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------------------------------------


-- padBuf --


/--
padBuf extends buf until it's size is sz by appending vals
-/
def padBuf (buf : Buf) (sz : Nat) (val : Byte) : Buf :=
  if sz <= buf.size
  then buf
  else
    let padding := Array.mkArray (sz - Array.size buf) val
    Array.append buf padding

-- padBuf is a noop if sz <= buf.size
theorem padBuf_noop_sz_lt : ∀ buf sz val, sz ≤ buf.size → padBuf buf sz val = buf := by
  intro buf sz val h
  unfold padBuf
  simp [*]

-- padBuf expands to sz if buf.size < sz
theorem padBuf_size_eq_sz buf sz val (h : sz > buf.size) : (padBuf buf sz val).size = sz := by
  unfold padBuf
  simp [Nat.not_le_of_lt h]
  unfold Array.size; simp
  rw [←Nat.add_sub_assoc, Nat.add_sub_self_left]
  apply Nat.le_of_lt h

-- padBuf buf sz val is never smaller than buf
theorem padBuf_never_decreases_size
  : ∀ buf sz val
  , buf.size ≤ (padBuf buf sz val).size := by
    intro buf sz val
    unfold padBuf
    by_cases hsz : sz ≤ buf.size
    · simp [hsz]
    · simp [hsz]
      unfold mkArray
      unfold Array.size
      simp

-- buf is a prefix of padBuf buf sz val
theorem padBuf_only_appends b s v i
  (h₁ : i < b.size)
  (h₂ : i < (padBuf b s v).size := Nat.lt_of_lt_of_le h₁ (padBuf_never_decreases_size b s v))
  : b[i]'h₁ = (padBuf b s v)[i]'h₂ := by
    unfold padBuf
    simp
    by_cases hsz : s ≤ b.size
    · simp [hsz]
    · simp [hsz]
      simp [Array.get_append_left h₁]

-- all elements past buf.size in the padded buffer are val
theorem padBuf_fills_vals buf sz val i
  (hsz : sz > buf.size)
  (hmin : buf.size ≤ i)
  (hmax : i < sz)
  (hidx : i < (padBuf buf sz val).size
    := lt_of_lt_of_eq hmax (Eq.symm $ padBuf_size_eq_sz buf sz val hsz))
  : (padBuf buf sz val)[i]'(hidx) = val := by
    unfold padBuf
    simp [Nat.not_le_of_lt hsz]
    simp [Array.get_append_right hmin]


-- joinBytes --


def joinBytes (bytes : Subarray (BitVec b)) : BitVec (bytes.size * b) :=
  BitVec.cast (by simp) $ go bytes.size (by rfl) BitVec.nil
  where
    go {m : ℕ} (n : Nat) (thm : n <= bytes.size) (res : BitVec m) : BitVec (m + (n * b))
    := match n with
    | 0 => BitVec.cast (by simp) res
    | Nat.succ x
      => let n := Nat.succ x
         have add_thm : m + b + (x * b) = m + Nat.succ x * b := by
           simp [Nat.succ_mul, Nat.add_assoc]
           simp [Nat.add_comm]
         have idx_thm : bytes.size - n < bytes.size := by
           have npos : 0 < n := by simp
           have szpos : 0 < bytes.size := Nat.lt_of_lt_of_le npos thm
           apply Nat.sub_lt
           apply szpos
           assumption
         let next := BitVec.append res (bytes[bytes.size - n]'(idx_thm))
         BitVec.cast add_thm $ go x (Nat.le_of_succ_le thm) next


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
        by_cases hsz : n + 32 <= buf.size
        · simp [hsz]
        · simp [hsz]
          unfold Array.size
          simp
          simp [Nat.lt_of_not_le] at hsz
          rw [←Nat.add_sub_assoc, Nat.add_sub_cancel_left]
          apply Nat.le_of_lt
          assumption
    }
  let res_thm : BitVec (bytes.size * 8) = Word := by
    have : bytes.size = 32 := by unfold Subarray.size; simp
    simp [this]
  res_thm ▸ joinBytes bytes

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
