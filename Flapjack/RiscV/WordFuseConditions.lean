import Flapjack.RiscV.Allocator
import Flapjack.RiscV.WordExpressionFlatten

/-!
Production implements original word_simp compile_exp through Seq_assoc,
const_fp, simp_duplicate_if and push_out_if. The extended WordProg carrier
prevents claiming a tagged native HOL port here. The separate list/fact fusion
helpers are legacy Flapjack infrastructure and are not part of that executed
composition; their presence does not establish original HOL correspondence.
-/

namespace Flapjack.RiscV

open Flapjack

/-- A variable known to hold the 0/1 result of a comparison. -/
structure WordConditionFact (α : Type u) where
  name : Nat
  operator : Cmp
  condition : Nat
  right : WordRegImm α
  deriving Repr

def wordConditionFactLookup [BEq α] (facts : List (WordConditionFact α))
    (name : Nat) : Option (WordConditionFact α) :=
  facts.find? (fun fact => fact.name == name)

def wordConditionFactSet (facts : List (WordConditionFact α)) (name : Nat)
    (value : Option (WordConditionFact α)) : List (WordConditionFact α) :=
  let cleared := facts.filter (fun fact => fact.name != name)
  match value with
  | some fact => { fact with name := name } :: cleared
  | none => cleared

/-- Drop every fact whose variable or whose comparison operands are written by
the given statement.  A fact records that a variable holds the truth of
`condition = right`, so it survives only while both the variable and the
operands keep their values. -/
def wordConditionFactInvalidate (facts : List (WordConditionFact α))
    (written : List Nat) : List (WordConditionFact α) :=
  facts.filter (fun fact =>
    !(written.contains fact.name) &&
      !(written.contains fact.condition) &&
      (match fact.right with
       | .imm _ => true
       | .reg register => !(written.contains register)))

/-- Transfer comparison facts across Cake's parallel `Move` carrier.  All
destinations are invalidated before looking up sources, while the lookups use
the pre-move fact set; this preserves the source semantics for a parallel
move whose source is also a destination. -/
def wordConditionFactMove [BEq α] (facts : List (WordConditionFact α))
    (moves : List (Nat × Nat)) : List (WordConditionFact α) :=
  let destinations := moves.map Prod.fst
  let remaining := wordConditionFactInvalidate facts destinations
  moves.foldl
    (fun current (destination, source) =>
      match wordConditionFactLookup remaining source with
      | some fact => wordConditionFactSet current destination (some fact)
      | none => wordConditionFactSet current destination none)
    remaining

end Flapjack.RiscV
