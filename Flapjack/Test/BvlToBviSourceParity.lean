import Flapjack.Compiler.Backend.BvlToBvi.SourceSing

/-! Replays the typed HOL auxiliary-tree observations. -/
open Flapjack Flapjack.Compiler.Backend.BvlToBvi

#guard match compileAuxSource (2, true, .var 1) with
  | .list [(81, true, .var 1)] => true
  | _ => false

#guard match compileSingSource 0
    (.ifThenElse (.let [] (.let [] (.var 0)))
      (.let [] (.let [] (.var 0))) (.let [] (.let [] (.var 0)))) with
  | (.ifThenElse (.call 0 (some 73) [] none) (.call 0 (some 77) [] none)
        (.call 0 (some 81) [] none),
      .append (.append (.list [(73, 0, .var 0)]) (.list [(77, 0, .var 0)]))
        (.list [(81, 0, .var 0)]), 3) => true
  | _ => false
