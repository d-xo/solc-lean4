import Lean
open Lean

-- Syntax --

declare_syntax_cat statement
declare_syntax_cat expression
declare_syntax_cat literal

syntax num : literal
syntax ident "(" literal,* ")" : statement
syntax "assembly {" ident "(" literal,* ")" "}" : doElem

-- Semantics --

instance : Coe Syntax (TSyntax `doElem) where
  coe s := ⟨s⟩

instance : Coe (Array Syntax) (TSyntax `Lean.Parser.Term.doSeq) where
  coe s := ⟨Elab.Term.Do.mkDoSeq s⟩

macro_rules
  | `(literal | $n:num) => `(doElem | pure $n)
  | `(doElem | assembly { $fn:ident( $xs:literal,* ) })
      => do
        -- grab only the args from the sep array
        let args := Syntax.TSepArray.getElems xs

        -- macro expand the args and generate a unique name for the result
        let exps ← Array.mapIdxM args $ λ idx arg => do
          let exp ← expandMacros arg
          let nm := idx |> .num (.str .anonymous "_arg") |> mkIdent
          let syn ← `(doElem | let ($nm) ← $exp)
          pure (nm, syn)

        -- yul evaluates function args right to left, so we reverse
        let calls := Array.map Prod.snd exps |> Array.reverse

        -- call fn with the result of evaluating it's arguments
        let results := Array.map Prod.fst exps

        let info ← MonadRef.mkInfoFromRefPos
        let exec := Syntax.node1 info `Lean.Parser.Term.doExpr (Syntax.mkApp fn results)
        let seq := Array.push calls exec
        dbg_trace exec
        `(doElem | do $seq)

-- Test Case --

def foo : Id Nat := pure 10

set_option pp.rawOnError true
#check `(do assembly { foo(1,2) })
#check do
  assembly {
    foo(1,2)
  }
