import Flapjack.SemanticPrimitivesHOL.PatternMatch

/-! Pattern-matching observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourcePatternParity
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

private def emptyC : NamespaceHOL.Namespace AstHOL.ModN AstHOL.ConN (Nat × Stamp) := .bind [] []
private def ctorC (arity : Nat) : NamespaceHOL.Namespace AstHOL.ModN AstHOL.ConN (Nat × Stamp) :=
  .bind [(ofString "A", (arity, .typeStamp (ofString "A") 7))] []
private def intV (n : Int) : Value := .litv (.intLit n)

#guard match pmatch emptyC [] (.pvar (ofString "x")) (intV 4) [] with
  | .match [(name, .litv (.intLit 4))] => name == ofString "x"
  | _ => false
#guard match pmatch (ctorC 0) [] (.pcon (some (.short (ofString "A"))) [])
    (.conv (some (.typeStamp (ofString "B") 7)) []) [] with
  | .noMatch => true
  | _ => false
#guard match pmatch (ctorC 1) [] (.pcon (some (.short (ofString "A"))) [])
    (.conv (some (.typeStamp (ofString "B") 7)) []) [] with
  | .typeError => true
  | _ => false
#guard match pmatchList emptyC [] [.plit (.intLit 1), .plit (.intLit 0)]
    [intV 2, .litv (.char 97)] [] with
  | .typeError => true
  | _ => false
#guard match pmatch emptyC [.refv (intV 4)] (.pref (.pvar (ofString "x"))) (.loc true 0) [] with
  | .match [(name, .litv (.intLit 4))] => name == ofString "x"
  | _ => false
#guard match pmatch emptyC [] (.pref (.pvar (ofString "x"))) (.loc true 0) [] with
  | .typeError => true
  | _ => false
#guard canPmatchAll emptyC [] [.plit (.intLit 1)] (intV 2)
#guard !canPmatchAll emptyC [] [.plit (.intLit 1)] (.litv (.char 97))

end Flapjack.Test.CakeSourcePatternParity
