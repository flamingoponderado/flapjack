module

public import Flapjack.Compiler.Backend.ClosCall.Stubs
public import Flapjack.Compiler.Backend.ClosCall.Calls
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Compiler.Backend.ClosCall.Proofs.GroupClosed

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.BackendCommon.Trace
public meta import Flapjack.Compiler.Backend.ClosCall
public meta import Flapjack.Compiler.Backend.ClosLang.Syntax
public meta import Flapjack.Compiler.Backend.ClosCall.Calls
public meta import Flapjack.Compiler.Backend.ClosCall.Compile
public meta import Flapjack.Compiler.Backend.ClosCall.Proofs.GroupClosed
@[expose] public section

/-! Replay original `clos_call_frontend_probe.out` cases. -/
namespace Flapjack.Test.ClosCallParity
open Flapjack.Compiler.Backend ClosCall
open Flapjack.Basis.Pure.MlString

-- `clos_call_stub_probe.out`: source stubs keep function order and use odd
-- locations, with arguments in ascending de Bruijn order.
#guard match callsListSource .none 4 10 [(2, true), (0, false), (1, true)] with
  | [(2, .call .none 0 11 [.var .none 0, .var .none 1]),
     (0, .call .none 0 13 []), (1, .call .none 0 15 [.var .none 0])] => true
  | _ => false

#guard match callsList 10 [(2, .var .none 7), (0, .var .none 8), (1, .var .none 9)] with
  | [(2, .call .none 0 11 [.var .none 0, .var .none 1]),
     (0, .call .none 0 13 []), (1, .call .none 0 15 [.var .none 0])] => true
  | _ => false

-- `clos_call_free_correct_probe.out`: matching function and body counts
-- agree with HOL's EVERY2 test, including rejection of an open body.
#guard groupClosedFuel 100 [(1, .var .none 0), (2, .var .none 1)]
    [.var .none 0, .var .none 1] == some true
#guard groupClosedFuel 100 [(1, .var .none 0), (2, .var .none 1)]
    [.var .none 0, .var .none 2] == some false

-- The fold zips its inputs; the pass proof establishes equal lengths before
-- comparing it with EVERY2, which rejects mismatched lists.
#guard groupClosedFuel 100 [(1, .var .none 0), (2, .var .none 1)]
    [.var .none 0] == some true
example : ¬ List.Forall₂
    (fun (fn : Nat × ClosLang.Exp) (e : ClosLang.Exp) =>
      ∀ n, ClosProps.freeVarExp n e → n < fn.1)
    [(1, .var .none 0), (2, .var .none 1)] [.var .none 0] := by
  simp

-- `clos_call_free_correct_probe.out`: bound arguments and let-bound values
-- do not count as captured variables, while references beyond them do.
#guard closedFuel 100 (.fn (ofString "f") (some 4) none 2 (.var .none 1)) == some true
#guard closedFuel 100 (.fn (ofString "f") (some 4) none 2 (.var .none 2)) == some false
#guard closedFuel 100 (.fn (ofString "f") (some 4) none 1
    (.let .none [.var .none 0] (.var .none 1))) == some true
#guard closedFuel 100 (.fn (ofString "f") (some 4) none 1
    (.let .none [.var .none 0] (.var .none 2))) == some false

-- `clos_call_code_list_probe.out`: preserve existing code and prepend new
-- bodies in reverse order, with the original odd-offset labels.
#guard match codeList 10 [(2, .var .none 4), (0, .var .none 9), (1, .var .none 2)]
    (.ln, [(90, 3, .var .none 0)]) with
  | (.ln, [(15, 1, .var .none 2), (13, 0, .var .none 9),
      (11, 2, .var .none 4), (90, 3, .var .none 0)]) => true
  | _ => false

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

-- The total traversal replays the original HOL closed, open, application and
-- recursive-group results independently of the bounded executable.
#guard match callsSing (.fn (ofString "f") (some 4) none 1 (.var .none 0)) (.ln, []) with
  | (.fn name (some 4) none 1 (.call .none 0 5 [.var .none 0]), (set, [(5, 1, .var .none 0)])) =>
      decide (name = ofString "f") && sptToAList set == [(4, ())]
  | _ => false
#guard match callsSing (.fn (ofString "f") (some 4) none 1 (.var .none 2)) (.ln, []) with
  | (.fn name (some 4) none 1 (.var .none 2), (set, [])) =>
      decide (name = ofString "f") && (sptToAList set).isEmpty
  | _ => false
#guard match callsSing (.app .none (some 4) (.var .none 0) [.var .none 1, .var .none 2]) state,
    callsSing (.app .none (some 4) (.tick .none (.var .none 0)) [.var .none 1, .var .none 2]) state with
  | (.call .none 2 5 [.var .none 1, .var .none 2], _),
    (.let .none [.var .none 1, .var .none 2, .tick .none (.var .none 0)]
      (.call .none 2 5 [.var .none 0, .var .none 1]), _) => true
  | _, _ => false
#guard match callsSing (.letrec [ofString "f", ofString "g"] (some 10) none
    [(1, .var .none 0), (1, .var .none 0)] (.var .none 0)) (.ln, []) with
  | (.letrec names (some 10) none
      [(1, .call .none 0 11 [.var .none 0]), (1, .call .none 0 13 [.var .none 0])] (.var .none 0),
      (set, [(13, 1, .var .none 0), (11, 1, .var .none 0)])) =>
      decide (names = [ofString "f", ofString "g"]) && sptToAList set == [(12, ()), (10, ())]
  | _ => false

-- `incremental` in the HOL probe: the input auxiliary code is replaced,
-- existing known locations are preserved, and a closed function adds its code.
private def incrementalProgram : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp) :=
  ([.fn (ofString "f") (some 4) none 1 (.var .none 0)], [(99, 1, .var .none 0)])

#guard match condCallCompileInc false (sptInsert 2 () .ln) incrementalProgram with
  | (set, ([.fn name (some 4) none 1 (.var .none 0)], [(99, 1, .var .none 0)])) =>
      decide (name = ofString "f") && sptToAList set == [(2, ())]
  | _ => false

#guard match condCallCompileInc true (sptInsert 2 () .ln) incrementalProgram with
  | (set, ([.fn name (some 4) none 1 (.call .none 0 5 [.var .none 0])],
      [(5, 1, .var .none 0)])) =>
      decide (name = ofString "f") && sptToAList set == [(4, ()), (2, ())]
  | _ => false

#guard match compileIncFuel? 0 (sptInsert 2 () .ln) incrementalProgram with
  | some (set, ([.fn name (some 4) none 1 (.call .none 0 5 [.var .none 0])],
      [(5, 1, .var .none 0)])) =>
      decide (name = ofString "f") && sptToAList set == [(4, ()), (2, ())]
  | _ => false

#guard compileIncFuel? 0 (sptInsert 2 () .ln) incrementalProgram ==
  compileIncFuel? 100 (sptInsert 2 () .ln) incrementalProgram

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
