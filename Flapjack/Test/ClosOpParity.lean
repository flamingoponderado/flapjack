import Flapjack.Compiler.Backend.ClosOp

/-! Replay complete `clos_op_frontend_probe.out` examples. -/
namespace Flapjack.Test.ClosOpParity
open Flapjack.Compiler.Backend

private def c (i : Int) : ClosLang.Exp := .op .none (.intOp (.const i)) []
private def cons (tag : Nat) (xs : List ClosLang.Exp) : ClosLang.Exp := .op .none (.blockOp (.cons tag)) xs

#guard match (do
    let a ← ClosOp.smartFuel 100 (.sourceLoc 1 2 3 4) (.intOp .div) [c (-3), c 7]
    let b ← ClosOp.smartFuel 100 .none (.intOp .div) [c 0, c 7]
    let d ← ClosOp.smartFuel 100 .none (.blockOp (.elemAt 0)) [cons 2 [.var .none 0, .var .none 1]]
    let e ← ClosOp.smartFuel 100 .none (.blockOp (.tagLenEq 2 2)) [cons 2 [.var .none 0, .var .none 1]]
    let f ← ClosOp.smartFuel 100 (.sourceLoc 1 2 3 4) (.blockOp .equal) [.var .none 0, .var .none 1]
    let g ← ClosOp.smartFuel 100 .none (.blockOp .equal) [c 2, .var .none 0]
    let h ← ClosOp.smartFuel 100 .none (.blockOp .equal) [cons 2 [], .var .none 0]
    let i ← ClosOp.smartFuel 100 .none (.blockOp .equal) [cons 2 [c 3, cons 4 []], .var .none 5]
    let j ← ClosOp.smartFuel 100 .none (.blockOp .equal) [cons 2 [.tick .none (.var .none 0)], cons 2 [.var .none 1]]
    let k ← ClosOp.smartFuel 100 .none (.blockOp .equal) [cons 2 [c 1], cons 3 [c 1]]
    let l ← ClosOp.smartFuel 100 .none (.blockOp .equal) [cons 2 [c 1, c 2], cons 2 [c 1, c 3]]
    let m ← ClosOp.smartFuel 100 .none (.blockOp .equal) [.var .none 5, cons 2 [c 3, cons 4 []]]
    pure [a, b, d, e, f, g, h, i, j, k, l, m]) with
  | some [.op .none (.intOp (.const (-3))) [], .op .none (.intOp (.const 0)) [],
      .let .none [.var .none 0, .var .none 1] (.var .none 1),
      .let .none [.var .none 0, .var .none 1] (.op .none (.blockOp (.cons 1)) []),
      .op (.sourceLoc 1 2 3 4) (.blockOp .equal) [.var .none 0, .var .none 1],
      .op .none (.blockOp (.equalConst (.int 2))) [.var .none 0],
      .op .none (.blockOp (.tagLenEq 2 0)) [.var .none 0],
      .let .none [.var .none 5]
        (.ifThenElse .none (.op .none (.blockOp (.tagLenEq 2 2)) [.var .none 0])
          (.ifThenElse .none (.op .none (.blockOp (.tagLenEq 4 0)) [.op .none (.blockOp (.elemAt 0)) [.var .none 0]])
            (.op .none (.blockOp (.equalConst (.int 3))) [.op .none (.blockOp (.elemAt 1)) [.var .none 0]])
            (.op .none (.blockOp (.cons 0)) [])) (.op .none (.blockOp (.cons 0)) [])),
      .let .none [.tick .none (.var .none 0), .var .none 1]
        (.op .none (.blockOp .equal) [.var .none 0, .var .none 1]),
      .let .none [] (.op .none (.blockOp (.cons 0)) []),
      .let .none [] (.ifThenElse .none (.op .none (.blockOp (.cons 0)) [])
        (.op .none (.blockOp (.cons 1)) []) (.op .none (.blockOp (.cons 0)) [])),
      .let .none [.var .none 5]
        (.ifThenElse .none (.op .none (.blockOp (.tagLenEq 2 2)) [.var .none 0])
          (.ifThenElse .none (.op .none (.blockOp (.tagLenEq 4 0)) [.op .none (.blockOp (.elemAt 0)) [.var .none 0]])
            (.op .none (.blockOp (.equalConst (.int 3))) [.op .none (.blockOp (.elemAt 1)) [.var .none 0]])
            (.op .none (.blockOp (.cons 0)) [])) (.op .none (.blockOp (.cons 0)) []))] => true
  | _ => false

end Flapjack.Test.ClosOpParity
