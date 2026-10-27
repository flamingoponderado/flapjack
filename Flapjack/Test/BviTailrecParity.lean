import Flapjack.Compiler.Backend.BviTailrec

/-! Replay the `cases` rows of `bvi_tailrec_frontend_probe.out`. -/
namespace Flapjack.Test.BviTailrecParity
open Flapjack.Compiler.Backend BviTailrec

#guard [
    Bvi.Exp.call 0 (some 3) [] none,
    .op (.intOp .add) [.call 0 (some 3) [] none, .var 0],
    .let [.op (.intOp .add) [.call 0 (some 3) [] none, .var 0]] (.var 0),
    .ifThenElse (.var 0) (.op (.intOp .add) [.call 0 (some 3) [] (some (.var 1)), .var 0]) (.var 1)
  ].map (hasRecFuel 100 3) == [some false, some true, some false, some false]

#guard (compileNoRecFuel 100 true 58
  [(3, 1, .op (.intOp .add) [.call 0 (some 3) [] none, .var 0])]).isNone
#guard match compileNoRecFuel 100 false 58
    [(3, 1, .op (.intOp .add) [.call 0 (some 3) [] none, .var 0])] with
  | some (58, [(3, 1, .op (.intOp .add) [.call 0 (some 3) [] none, .var 0])]) => true
  | _ => false

end Flapjack.Test.BviTailrecParity
