import Lean.Parser.Command
import Lean

open Lean Macro Elab

--open Lean Parser Term
--declare_syntax_cat type_spec

---- Works :)
--syntax (ident+),+ : type_spec

----▶ 7:16-7:17: error:
----unexpected token '→'; expected ':'
--syntax (ident+)→+ : type_spec

def f := Fin.last 5

def r := Fin.mod (f + f) 4

def ns := (5 + 5) % 4

def hi : MacroM Lean.Syntax := do
  `(Lean.Parser.Command.optDeclSig | a)


#check hi
#eval f
#eval r
#eval ns
