import Flapjack.Compiler.Backend.BvlHandle.Compile

/-! Replay examples from `bvl_handle_frontend_probe.out`. -/
namespace Flapjack.Test.BvlHandleParity
open Flapjack.Compiler.Backend BvlHandle

#guard match [
    Bvl.Exp.handle (.let [.var 0] (.raise (.var 0))) (.var 1),
    .handle (.ifThenElse (.var 0) (.raise (.var 1)) (.var 2)) (.var 1),
    .handle (.call 0 (some 2) []) (.force 9 1)].mapM (simplifyFuel 100) with
  | some [.let [.var 0] (.let [.var 0] (.var 2)),
      .ifThenElse (.var 0) (.let [.var 1] (.var 1)) (.var 2),
      .handle (.call 0 (some 2) []) (.force 9 1)] => true
  | _ => false

#guard match [
    Bvl.Exp.handle (.call 0 (some 2) [.var 2, .var 0]) (.var 1),
    .handle (.var 1) (.var 0), .force 4 9].mapM (compileFuel 100 20 3) with
  | some [(.handle (.let [.var 0, .var 2] (.let [.var 0, .op (.intOp (.const 0)) [], .var 1]
          (.call 0 (some 2) [.var 2, .var 0]))) (.var 1),
        .union (.union (.var 2) (.var 0)) (.shift 1 (.var 1)), 1, true),
      (.var 1, .var 1, 1, true), (.op (.intOp (.const 0)) [], .empty, 1, true)] => true
  | _ => false

#guard match compileFuel 100 2 3 (.call 0 (some 4) [.var 2, .var 0]) with
  | some (.let [] (.let [.var 0, .var 2] (.let [.var 0, .op (.intOp (.const 0)) [], .var 1]
        (.call 0 (some 4) [.var 2, .var 0]))),
      .union (.var 2) (.union (.var 0) .empty), 0, false) => true
  | _ => false

-- Replay the same original observations through the total source traversal.
#guard match [
    Bvl.Exp.handle (.call 0 (some 2) [.var 2, .var 0]) (.var 1),
    .handle (.var 1) (.var 0), .force 4 9].map (compileSing 20 3) with
  | [(.handle (.let [.var 0, .var 2] (.let [.var 0, .op (.intOp (.const 0)) [], .var 1]
          (.call 0 (some 2) [.var 2, .var 0]))) (.var 1),
        .union (.union (.var 2) (.var 0)) (.shift 1 (.var 1)), 1, true),
      (.var 1, .var 1, 1, true), (.op (.intOp (.const 0)) [], .empty, 1, true)] => true
  | _ => false

#guard match compileSing 2 3 (.call 0 (some 4) [.var 2, .var 0]) with
  | (.let [] (.let [.var 0, .var 2] (.let [.var 0, .op (.intOp (.const 0)) [], .var 1]
        (.call 0 (some 4) [.var 2, .var 0]))),
      .union (.var 2) (.union (.var 0) .empty), 0, false) => true
  | _ => false
#guard (simplifyFuel 0 (.var 0)).isNone
#guard match compileAnyWithoutConstantsFuel 100 true 100 0
    (.let [.call 0 (some 1) [], .call 0 (some 2) []] (.var 1)) with
  | some (.let [.call 0 (some 1) []] (.let [] (.let [] (.call 0 (some 2) [])))) => true
  | _ => false

end Flapjack.Test.BvlHandleParity
