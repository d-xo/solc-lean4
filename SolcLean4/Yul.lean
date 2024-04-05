import Std.Data.HashMap
import Lean

open Lean Elab Meta

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

syntax yul_identifier "(" (yul_expression ("," yul_expression)* )? ")" : yul_expression
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
  rep : Nat

namespace Word

def abs := Word.mk

end Word

instance : BEq Word where
  beq a b := a.rep == b.rep

instance : Hashable Word where
  hash n := hash n.rep

instance : Repr Word where
  reprPrec w := reprPrec w.rep

-- Semantics --

syntax "assembly " yul_block : doElem

instance : Coe Syntax (TSyntax `doElem) where
  coe s := ⟨s⟩

instance : Coe (Array Syntax) (TSyntax `Lean.Parser.Term.doSeq) where
  coe s := ⟨Elab.Term.Do.mkDoSeq s⟩

def prepend_yul : (i : TSyntax `ident) → Option (TSyntax `ident)
  | `($i:ident) => match i.raw with
    | Syntax.ident _ _ nm _ => some $ mkIdent (Name.appendBefore nm "yul_")
    | _ => none
  | _ => none

macro_rules
  | `(yul_literal | true) => `(doElem | pure Bool.true)
  | `(yul_literal | false) => `(doElem | pure Bool.false)
  | `(yul_literal | $n:num) => `(doElem | pure $ Word.abs $n)
  | `(yul_identifier | $i:ident) => `(doElem | pure $i)
  | `(yul_block | { $s:yul_statement* }) => do
      let ss ← Array.mapM expandMacros s
      `(doElem | do $ss)
  | `(doElem | assembly $b:yul_block) => expandMacros b
  | `(yul_statement | $i:ident := $e:yul_expression)
      => do
        let ee ← Lean.expandMacros e
        `(doElem | ($i) ← $ee)
  | `(yul_statement | $e:yul_expression)
      => do
        let ee ← Lean.expandMacros e
        `(doElem | _ ← $ee)
  | `(yul_expression | $l:yul_literal) => do
      let le ← Lean.expandMacros l
      `(doElem | $le)
  | `(yul_expression | $i:yul_identifier) => do
      let ie ← Lean.expandMacros i
      `(doElem | $ie)
  | `(yul_expression | $i:ident($x:yul_expression,$y:yul_expression))
      => do
        let xe ← expandMacros x
        let ye ← expandMacros y
        match prepend_yul i with
        | some nm =>
          `(doElem | do
             let y' ← $ye
             let x' ← $xe
             ($nm) x' y'
           )
        | none => Macro.throwUnsupported

-- EVM Execution Environment & OpCodes --

structure EVM where
  memory : List UInt8
  calldata : List UInt8
  returndata : List UInt8
  storage : Std.HashMap Word Word
abbrev Yul (a : Type) : Type := StateM EVM a
abbrev Sol a := Yul a

def emptyEVM := EVM.mk [] [] [] Std.HashMap.empty

def runSol (s : Sol a) : a := Prod.fst $ Id.run (StateT.run s emptyEVM)

def yul_add (a : Word) (b : Word) : Yul Word :=
  pure (Word.abs ((a.rep + b.rep) % (2 ^ 256)))

#eval Id.run $ do
  let mut (x : Word) := Word.abs 0
  assembly { x := 15 }
  pure x


namespace Solidity

-- uint256 --

-- TODO: add a custom command to automate the boilerplate here...
structure U256 where
  rep : Word

instance : Repr U256 where
  reprPrec u := reprPrec u.rep

namespace U256

def abs := U256.mk

end U256


-- Addition --

class Add (t : Type) where
  add : t → t → Sol t

instance : Add U256 where
  add x y := do
    let xw := U256.rep x
    let yw := U256.rep y
    let mut zw := Word.abs 0
    assembly {
      zw := add(xw, yw)
    }
    return U256.abs zw

#eval runSol $ do
  Add.add (U256.abs (Word.abs 10)) (U256.abs (Word.abs 11))

end Solidity
