import Lean
open Lean

-- Syntax --

declare_syntax_cat statement
declare_syntax_cat literal

syntax num : literal
syntax ident ":=" literal : statement
-- I want to write `doElem*` on the RHS, but that's not valid...
syntax "assembly {" statement* "}" : doElem

-- Semantics --

instance : Coe (Syntax) (TSyntax `term) where
  coe s := ⟨s⟩

instance : Coe Syntax (TSyntax `doElem) where
  coe s := ⟨s⟩

instance : Coe (Array Syntax) (TSyntax `Lean.Parser.Term.doSeq) where
  coe s := ⟨Elab.Term.Do.mkDoSeq s⟩

macro_rules
  | `(literal | $n:num) => `(doElem | pure $n)
  | `(statement | $i:ident := $l:literal) => do
       let le ← Lean.expandMacros l
       `(doElem | ($i) ← $le)
  | `(doElem | assembly { $s:statement* }) => do
      let ss ← Array.mapM expandMacros s
      `(doElem | do $ss)

-- Test Case --

set_option pp.rawOnError true

def ex : Id Nat := do
  let mut x : Nat := 0
  assembly {
    x := 44
    x := 15
  }
  return x

-- should return 15
#eval Id.run ex
