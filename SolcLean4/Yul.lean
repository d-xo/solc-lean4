import Std.Data.HashMap
import Lean

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

-- Semantics --

syntax "assembly " yul_block : term

instance : Coe (TSyntax `yul_expression) (TSyntax `doElem) where
  coe s := ⟨s.raw⟩

instance : Coe (TSyntax `yul_expression) (TSyntax `term) where
  coe s := ⟨s.raw⟩

instance : Coe (TSyntax `yul_expression) (TSyntax `Lean.Parser.Term.doSeqItem) where
  coe s := ⟨s.raw⟩

instance : Coe (TSyntax `yul_statement) (TSyntax `Lean.Parser.Term.doSeqItem) where
  coe s := ⟨s.raw⟩

instance : Coe (TSyntax `ident) (TSyntax `Lean.Parser.Term.doSeqItem) where
  coe s := ⟨s.raw⟩

instance : Coe (TSyntax `yul_block) (TSyntax `term) where
  coe s := ⟨s.raw⟩

instance : Coe (TSyntax `yul_literal) (TSyntax `term) where
  coe s := ⟨s.raw⟩

macro_rules
  | `(yul_literal | true) => `(pure Bool.true)
  | `(yul_literal | false) => `(pure Bool.false)
  | `(yul_literal | $n:num) => `(pure $ Word.abs $n)
  | `(assembly $b:yul_block) => `($b)
  | `(yul_block | { $[$s:yul_statement]* })
      => `(do
            $[$s]*
          )
  | `(yul_statement | $i:ident := $e:yul_expression)
      => `(do
            let e' ← $e
            $i ":=" e'
          )
  | `(yul_statement | $e:yul_expression)
      => `($e >> (pure ()))
  | `(yul_expression | $l:yul_literal) => `($l)
  | `(yul_expression | $i:ident($x:yul_expression,$y:yul_expression))
      => `(do
            let y' ← $y
            let x' ← $x
            yul_$i x' y'
          )
end Yul

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

-- EVM Execution Environment & OpCodes --

structure EVM where
  memory : List UInt8
  storage : Std.HashMap Word Word
abbrev Yul (a : Type) : Type := StateM EVM a
abbrev Sol a := Yul a

def yul_add (a : Word) (b : Word) : Yul Word :=
  pure (Word.abs ((a.rep + b.rep) % (2 ^ 256)))

#check do
  let mut (x : Word) := Word.abs 0
  assembly { add(10, 11) }
  pure x


namespace Solidity

-- uint256 --

structure U256 where
  rep : Word

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
    let mut z := U256
    -- This block needs to parse a mix of lean4 and yul into pure lean4.
    assembly { z := U256.abs(add(xw, yw)) }
    return z

end Solidity
