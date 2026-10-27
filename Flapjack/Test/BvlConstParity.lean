import Flapjack.Compiler.Backend.BvlConst

/-! Replay cases captured in `bvl_const_frontend_probe.out`. -/
namespace Flapjack.Test.BvlConstParity
open Flapjack.Compiler.Backend BvlConst

#guard [Int.fdiv 7 3, Int.fdiv (-7) 3, Int.fdiv 7 (-3), Int.fdiv (-7) (-3),
  Int.fmod 7 3, Int.fmod (-7) 3, Int.fmod 7 (-3), Int.fmod (-7) (-3)] ==
  [2, -3, -3, 2, 1, 2, -2, -1]
#guard match [
    smartOp (.intOp .add) [.var 0, .op (.intOp (.const 0)) []],
    smartOp (.intOp .sub) [.op (.intOp (.const 7)) [], .op (.intOp (.const 3)) []],
    smartOp (.intOp .div) [.op (.intOp (.const (-3))) [], .op (.intOp (.const 7)) []],
    smartOp (.blockOp .equal) [.var 0, .op (.intOp (.const 4)) []],
    smartOp (.memOp .el) [.op (.intOp (.const 2)) [], .var 1]] with
  | [.var 0, .op (.intOp (.const (-4))) [], .op (.intOp (.const (-3))) [],
     .op (.blockOp (.equalConst (.int 4))) [ .var 0 ], .op (.blockOp (.elemAt 2)) [.var 1]] => true
  | _ => false
#guard match compileFuel 100 [] (.let [.var 3, .op (.intOp (.const 5)) []]
    (.op (.intOp .add) [.var 0, .var 1])) with
  | some (.let [.op (.intOp (.const 0)) [], .op (.intOp (.const 5)) []]
      (.op (.intOp .add) [.var 5, .op (.intOp (.const 5)) []])) => true
  | _ => false

private def c (n : Int) : Bvl.Exp := .op (.intOp (.const n)) []
private def a (x y : Bvl.Exp) : Bvl.Exp := .op (.intOp .add) [x, y]
private def s (x y : Bvl.Exp) : Bvl.Exp := .op (.intOp .sub) [x, y]
private def m (x y : Bvl.Exp) : Bvl.Exp := .op (.intOp .mult) [x, y]
#guard match [smartOp (.intOp .add) [a (.var 0) (c 2), c 3],
    smartOp (.intOp .sub) [s (.var 0) (c 2), c 3],
    smartOp (.intOp .add) [a (.var 0) (c 2), s (.var 1) (c 3)],
    smartOp (.intOp .sub) [a (.var 0) (c 2), s (.var 1) (c 3)],
    smartOp (.intOp .mult) [m (.var 0) (c 2), m (.var 1) (c 3)],
    smartOp (.intOp .mod) [c (-3), c 7], smartOp (.intOp .less) [c 3, c 2],
    smartOp (.blockOp (.equalConst (.int 4))) [c 4]] with
  | [.op (.intOp .add) [.var 0, .op (.intOp (.const 5)) []],
     .op (.intOp .add) [.var 0, .op (.intOp (.const 1)) []],
     .op (.intOp .sub) [.op (.intOp .sub) [.var 0, .var 1], .op (.intOp (.const 5)) []],
     .op (.intOp .sub) [.op (.intOp .add) [.var 0, .var 1], .op (.intOp (.const 1)) []],
     .op (.intOp .mult) [.op (.intOp (.const 6)) [], .op (.intOp .mult) [.var 0, .var 1]],
     .op (.intOp (.const (-2))) [], .op (.blockOp (.cons 1)) [], .op (.blockOp (.cons 1)) []] => true
  | _ => false

end Flapjack.Test.BvlConstParity
