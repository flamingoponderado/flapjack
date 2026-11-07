import Flapjack.Compiler.Backend.PatternSemantics.Semantics

/-! Focused checks of the pattern compiler's abstract semantics. -/
namespace Flapjack.Test.PatternSemantics
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend.PatternCommon
open Flapjack.Compiler.Backend.PatternSemantics

private def refs : HolFiniteMapExact Nat Term :=
  (HolFiniteMapExact.empty : HolFiniteMapExact Nat Term).update (3, .litv (.intLit 7))

#guard dtTest (.litEq (.intLit 7)) (.litv (.intLit 7)) == some true
#guard dtTest (.litEq (.intLit 7)) (.litv (.intLit 8)) == some false
#guard dtTest (.litEq (.intLit 7)) (.term none []) == none
#guard (match appPos refs (.pos 0 .emptyPos) (.refPtr 3) with
  | some (.litv (.intLit 7)) => true | _ => false)
#guard (match appPos refs (.pos 1 .emptyPos) (.refPtr 3) with | none => true | _ => false)
#guard dtEvalGuard refs .other (.conj (.not .true_) (.posTest .emptyPos (.litEq (.intLit 1)))) == some false
#guard dtEvalGuard refs .other (.conj .true_ (.posTest .emptyPos (.litEq (.intLit 1)))) == none
#guard dtEvalGuard refs .other (.disj .true_ (.posTest .emptyPos (.litEq (.intLit 1)))) == some true
#guard dtEval refs .other (.if_ (.not .true_) (.leaf 1) (.leaf 2)) == some (.success 2)
#guard matchRows refs [(.any, 1), (.lit (.intLit 1), 2)] .other == none
#guard matchRows refs [(.lit (.intLit 1), 1), (.any, 2)] (.litv (.intLit 2)) == some (.success 2)

end Flapjack.Test.PatternSemantics
