import Flapjack.EvaluateHOL

/-! Typed clock-lemma replay and examples captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceEvaluateClock
open Flapjack Flapjack.EvaluateHOL Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

example (s : State Nat) (other : State Bool) (result : Char) :
    (fixClock s (other, result)).1.clock ≤ s.clock := by
  exact fixClockImp s _ result (other, result) rfl

example (s : State Nat) : (fixClock { s with clock := 3 } ({ s with clock := 7 }, true)).1.clock = 3 := by
  rfl

example (s : State Nat) : (decClock { s with clock := 0 }).clock = 0 := by
  rfl

#guard match listResult (Result.err (.raise 1) : Result Bool Nat) with
  | .err (.raise 1) => true
  | _ => false

#guard match NamespaceHOL.nsLookup (singleEnv (ofString "x") (.litv (.intLit 4))).v (.short (ofString "x")) with
  | some (.litv (.intLit 4)) => true
  | _ => false

end Flapjack.Test.CakeSourceEvaluateClock
