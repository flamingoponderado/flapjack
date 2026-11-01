import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ProgramAgreement
import Flapjack.Compiler.Backend.BvlToBvi.Incremental

/-! Replays the typed HOL auxiliary-tree observations. -/
open Flapjack Flapjack.Compiler.Backend.BvlToBvi

-- Replays the original two-call incremental pipeline, observing both
-- retained caches, the fresh-name counters, and each resulting program.
private def incrementalConfig : Config :=
  { defaultConfig with nextName1 := 2, nextName2 := 3, nextName3 := 4, doTailrec := false, doTmc := false }

#guard match compileIncAllFuel 100 incrementalConfig [(1, 1, .var 0)] with
  | some (config, [(76, 1, .var 0)]) =>
    match compileIncAllFuel 100 config [(2, 1, .call 0 (some 1) [.var 0])] with
    | some (next, [(80, 1, .let [.op (.intOp (.const 0)) []] (.var 1))]) =>
      next.nextName1 == 2 && next.nextName2 == 3 && next.nextName3 == 4 &&
        (sptToAList next.bviInlines).isEmpty &&
        match sptToAList next.inlines with
        | [(1, 1, .var 0), (2, 1, .let [.var 0] (.tick (.var 0)))] => true
        | _ => false
    | _ => false
  | _ => false

#guard match compileIncAllFuel 100 defaultConfig [(1, 1, .var 0)] with
  | some (config, [(76, 1, .var 0)]) =>
    config.nextName1 == 73 && config.nextName2 == 74 && config.nextName3 == 75 &&
      (sptToAList config.bviInlines).isEmpty &&
      match sptToAList config.inlines with
      | [(1, 1, .var 0)] => true
      | _ => false
  | _ => false

#guard match compileAuxSource (2, true, .var 1) with
  | .list [(81, true, .var 1)] => true
  | _ => false

-- This replays the original three-branch case through the executed retry.
#guard compileBounded 0 0 0
    (.ifThenElse (.let [] (.let [] (.var 0)))
      (.let [] (.let [] (.var 0))) (.let [] (.let [] (.var 0)))) ==
  some (.ifThenElse (.call 0 (some 73) [] none) (.call 0 (some 77) [] none)
      (.call 0 (some 81) [] none),
    [(73, 0, .var 0), (77, 0, .var 0), (81, 0, .var 0)], 3)

-- The original incremental compiler returns this code and fresh-name state.
#guard compileIncFuel 0 0 0 [(1, 2, .let [] (.let [] (.var 0))), (2, 1, .var 0)] ==
  some (1, [(76, 2, .call 0 (some 73) [] none), (73, 0, .var 0), (80, 1, .var 0)])

#guard match compileSingSource 0
    (.ifThenElse (.let [] (.let [] (.var 0)))
      (.let [] (.let [] (.var 0))) (.let [] (.let [] (.var 0)))) with
  | (.ifThenElse (.call 0 (some 73) [] none) (.call 0 (some 77) [] none)
        (.call 0 (some 81) [] none),
      .append (.append (.list [(73, 0, .var 0)]) (.list [(77, 0, .var 0)]))
        (.list [(81, 0, .var 0)]), 3) => true
  | _ => false
