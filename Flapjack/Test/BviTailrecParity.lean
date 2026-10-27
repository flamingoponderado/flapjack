import Flapjack.Compiler.Backend.BviTailrec.Analysis

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

private def c (n : Int) : Bvi.Exp := .op (.intOp (.const n)) []
private def self : Bvi.Exp := .call 0 (some 3) [.var 0] none
private def examples : List Bvi.Exp :=
  [.op (.intOp .add) [c 1, self],
   .op (.intOp .mult) [self, c 2],
   .op (.intOp .add) [.var 0, self],
   .let [.op (.intOp .less) [.var 0, c 4]] (.op (.intOp .add) [.var 1, self]),
   .op (.blockOp .listAppend) [.op (.blockOp (.cons 0)) [], self],
   .op (.intOp .add) [c 268435458, self]]

#guard match examples.mapM (fun e => do
    let result ← scanFuel 100 [.any] 3 e
    let decision ← checkExpFuel 100 3 1 e
    pure (result, decision)) with
  | some [(([.any], .int, false, some .plus), some .plus),
      (([.any], .int, false, some .times), some .times),
      (([.any], .any, false, none), none),
      (([.int], .int, false, some .plus), some .plus),
      (([.any], .list, false, some .append), some .append),
      (([.any], .any, false, none), none)] => true
  | _ => false

#guard (compileNoRewriteFuel 100 true 58 [(3, 1, .op (.intOp .add) [c 1, self])]).isNone
#guard match compileNoRewriteFuel 100 true 58 [(3, 1, .op (.intOp .add) [.var 0, self])] with
  | some (58, [_]) => true
  | _ => false

end Flapjack.Test.BviTailrecParity
