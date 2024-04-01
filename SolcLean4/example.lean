import Lean
open Lean

-- Syntax --

declare_syntax_cat statement
declare_syntax_cat literal

syntax ident ":=" num : statement
syntax "assembly {" statement "}" : doElem

-- Semantics --

macro_rules
  --| `(literal | $n:num) => `(pure $n)
  | `(statement | $i:ident := $n:num) => `(doElem | ($i) ← pure $n)
  | `(doElem | assembly { $s:statement }) => `(statement | $s)

-- Test Case --

def ex : Id Nat := do
  let mut x : Nat := 0
  assembly { x := 10 }
  return x
