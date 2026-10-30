import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ProgramAgreement

/-! Replays the typed HOL auxiliary-tree observations. -/
open Flapjack Flapjack.Compiler.Backend.BvlToBvi

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
