import Std.Data.HashMap
import Lean
import Lean.Parser
import Lean.Parser.Do

open Lean Elab Meta

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

-- The type of EVM words --

structure Word where
  abs ::
  -- TODO: would be cool to use Fin here maybe?
  rep : Nat
deriving Repr, Hashable, BEq

instance instOfNatWord (n : Nat) : OfNat Word n where
  ofNat := Word.abs n

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
  memory : List UInt8
  calldata : List UInt8
  returndata : List UInt8
  storage : Std.HashMap Yul.Word Yul.Word
abbrev Yul (a : Type) : Type := StateM EVM a

-- OpCodes --

def add (a : Word) (b : Word) : Yul Word :=
  pure (Word.abs ((a.rep + b.rep) % (2 ^ 256)))

def addmod (a : Word) (b : Word) (n : Word) : Yul Word :=
  pure (Word.abs ((a.rep + b.rep) % n.rep))

end Yul
