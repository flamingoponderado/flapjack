import Flapjack.Compiler.Backend.ClosCall

/-! Replay original `clos_call_frontend_probe.out` cases. -/
namespace Flapjack.Test.ClosCallParity
open Flapjack.Compiler.Backend ClosCall
open Flapjack.Basis.Pure.MlString

#guard match freeFuel 100 (.fn (ofString "f") (some 4) none 1
    (.let .none [.var .none 3] (.var .none 0))) with
  | some (.fn name (some 4) (some [2]) 1 (.let .none [.var .none 3] (.var .none 0)),
      .shift 1 (.union (.var 3) (.shift 1 (.var 0)))) => decide (name = ofString "f")
  | _ => false

#guard match callsFuel 100 (.fn (ofString "f") (some 4) none 1 (.var .none 0)) (.ln, []) with
  | some (.fn name (some 4) none 1 (.call .none 0 5 [.var .none 0]), (set, [(5, 1, .var .none 0)])) =>
      decide (name = ofString "f") && sptToAList set == [(4, ())]
  | _ => false
#guard match callsFuel 100 (.fn (ofString "f") (some 4) none 1 (.var .none 2)) (.ln, []) with
  | some (.fn name (some 4) none 1 (.var .none 2), (set, [])) =>
      decide (name = ofString "f") && (sptToAList set).isEmpty
  | _ => false

private def state : State := (sptInsert 4 () .ln, [])
#guard match callsFuel 100 (.app .none (some 4) (.var .none 0) [.var .none 1, .var .none 2]) state,
    callsFuel 100 (.app .none (some 4) (.tick .none (.var .none 0)) [.var .none 1, .var .none 2]) state with
  | some (.call .none 2 5 [.var .none 1, .var .none 2], _),
    some (.let .none [.var .none 1, .var .none 2, .tick .none (.var .none 0)]
      (.call .none 2 5 [.var .none 0, .var .none 1]), _) => true
  | _, _ => false

#guard match callsFuel 100 (.letrec [ofString "f", ofString "g"] (some 10) none
    [(1, .var .none 0), (1, .var .none 0)] (.var .none 0)) (.ln, []) with
  | some (.letrec names (some 10) none
      [(1, .call .none 0 11 [.var .none 0]), (1, .call .none 0 13 [.var .none 0])] (.var .none 0),
      (set, [(13, 1, .var .none 0), (11, 1, .var .none 0)])) =>
      decide (names = [ofString "f", ofString "g"]) && sptToAList set == [(12, ()), (10, ())]
  | _ => false

end Flapjack.Test.ClosCallParity
