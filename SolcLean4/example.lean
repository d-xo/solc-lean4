import Lean
open Lean

-- Syntax --

declare_syntax_cat statement
declare_syntax_cat literal

syntax num : literal
syntax ident ":=" literal : statement
syntax "assembly {" statement "}" : doElem

-- Semantics --

instance : Coe (Syntax) (TSyntax `term) where
  coe s := ⟨s⟩

macro_rules
  | `(literal | $n:num) => `(term | $n)
  | `(statement | $i:ident := $l:literal) => do
       let le ← Lean.expandMacros l
       `(doElem | ($i) ← pure $le)
  | `(doElem | assembly { $s:statement }) => `(statement | $s)

-- Test Case --

def ex : Id Nat := do
  let mut x : Nat := 0
  assembly { x := 44 }
  assembly { x := 15 }
  return x

#eval Id.run ex
