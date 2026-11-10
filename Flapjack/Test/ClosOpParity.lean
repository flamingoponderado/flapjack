module

public import Flapjack.Compiler.Backend.ClosOp

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.BackendCommon.Trace
public meta import Flapjack.Compiler.Backend.ClosLang.Syntax
public meta import Flapjack.Compiler.Backend.ClosOp
public meta import Flapjack.Misc.AppList
@[expose] public section

/-! Replay complete `clos_op_frontend_probe.out` examples. -/
namespace Flapjack.Test.ClosOpParity
open Flapjack.Compiler.Backend

private def c (i : Int) : ClosLang.Exp := .op .none (.intOp (.const i)) []
private def cons (tag : Nat) (xs : List ClosLang.Exp) : ClosLang.Exp := .op .none (.blockOp (.cons tag)) xs

-- `smart_stages` checks failure, fallback, direct equality and integer folding.
#guard match (ClosOp.eqAny (.var .none 0) (.var .none 1),
    ClosOp.eqOp (.var .none 0) (.var .none 1), ClosOp.eqOp (c 2) (.var .none 0),
    ClosOp.smartOp' (7 : Nat) (.blockOp .equal) [.var .none 0, .var .none 1],
    ClosOp.smartOp' (7 : Nat) (.intOp .add) [c 2, c 3],
    ClosOp.smartOp (.sourceLoc 1 2 3 4) (.blockOp .equal) [.var .none 0, .var .none 1]) with
  | (some (.let .none [.var .none 0, .var .none 1]
       (.op .none (.blockOp .equal) [.var .none 0, .var .none 1])), none,
     some (.op .none (.blockOp (.equalConst (.int 2))) [.var .none 0]), none,
     some (.op .none (.intOp (.const 5)) []),
     .op (.sourceLoc 1 2 3 4) (.blockOp .equal) [.var .none 0, .var .none 1]) => true
  | _ => false

-- `conj` checks empty, singleton and multi-element source clauses.
#guard match (ClosOp.conjList [], ClosOp.conjList [.var .none 0],
    ClosOp.conjList [.var .none 0, .var .none 1, .var .none 2],
    ClosOp.eqPure (.var .none 0) (.var .none 1)) with
  | (.op .none (.blockOp (.cons 1)) [], .var .none 0,
     .ifThenElse .none (.var .none 0)
       (.ifThenElse .none (.var .none 1) (.var .none 2) (.op .none (.blockOp (.cons 0)) []))
       (.op .none (.blockOp (.cons 0)) []),
     .op .none (.blockOp .equal) [.var .none 0, .var .none 1]) => true
  | _ => false

-- `eq_tree` checks the original tree shape and reversed field order.
#guard match [ClosOp.eqPureList [],
    ClosOp.eqPureList [(.var .none 0, .var .none 1)],
    ClosOp.eqPureList [(cons 2 [c 3, .var .none 0], .var .none 1)],
    ClosOp.eqPureList [(cons 2 [.var .none 0, .var .none 1], cons 2 [.var .none 2, .var .none 3])],
    ClosOp.eqPureList [(cons 2 [.var .none 0], cons 3 [.var .none 1])],
    ClosOp.eqPureList [(.var .none 0, .var .none 1), (c 4, .var .none 2)]] with
  | [.nil, .list [.op .none (.blockOp .equal) [.var .none 0, .var .none 1]],
     .append (.list [.op .none (.blockOp (.tagLenEq 2 2)) [.var .none 1]])
       (.append (.list [.op .none (.blockOp .equal)
         [.var .none 0, .op .none (.blockOp (.elemAt 0)) [.var .none 1]]])
         (.list [.op .none (.blockOp (.equalConst (.int 3)))
           [.op .none (.blockOp (.elemAt 1)) [.var .none 1]]])),
     .append (.list [.op .none (.blockOp .equal) [.var .none 1, .var .none 3]])
       (.list [.op .none (.blockOp .equal) [.var .none 0, .var .none 2]]),
     .list [.op .none (.blockOp (.cons 0)) []],
     .append (.list [.op .none (.blockOp .equal) [.var .none 0, .var .none 1]])
       (.list [.op .none (.blockOp (.equalConst (.int 4))) [.var .none 2]])] => true
  | _ => false

-- `lift` preserves source-order effects and retains the supplied accumulator.
#guard match ClosOp.liftExpsHOL [] 2 [.var .none 7] with
  | ([], 2, [.var .none 7]) => true
  | _ => false

#guard match ClosOp.liftExpsHOL
    [cons 2 [.tick .none (.var .none 0), c 3], .var .none 4, c 5]
    4 [.var .none 7] with
  | ([.op .none (.blockOp (.cons 2)) [.var .none 4, .op .none (.intOp (.const 3)) []],
      .var .none 5, .op .none (.intOp (.const 5)) []],
     6, [.var .none 7, .tick .none (.var .none 0), .var .none 4]) => true
  | _ => false

-- `signed` checks both operations for all sign combinations and zero divisors.
#guard match [ClosOp.integerOp (.intOp .div) 3 7,
    ClosOp.integerOp (.intOp .div) (-3) 7,
    ClosOp.integerOp (.intOp .div) 3 (-7),
    ClosOp.integerOp (.intOp .div) (-3) (-7),
    ClosOp.integerOp (.intOp .mod) 3 7,
    ClosOp.integerOp (.intOp .mod) (-3) 7,
    ClosOp.integerOp (.intOp .mod) 3 (-7),
    ClosOp.integerOp (.intOp .mod) (-3) (-7),
    ClosOp.integerOp (.intOp .div) 0 (-7),
    ClosOp.integerOp (.intOp .mod) 0 (-7)] with
  | [some (.op .none (.intOp (.const 2)) []),
     some (.op .none (.intOp (.const (-3))) []),
     some (.op .none (.intOp (.const (-3))) []),
     some (.op .none (.intOp (.const 2)) []),
     some (.op .none (.intOp (.const 1)) []),
     some (.op .none (.intOp (.const (-2))) []),
     some (.op .none (.intOp (.const 2)) []),
     some (.op .none (.intOp (.const (-1))) []),
     some (.op .none (.intOp (.const 0)) []),
     some (.op .none (.intOp (.const 0)) [])] => true
  | _ => false

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

-- Exercise the structural retries with nested constructors in both orders.
#guard (ClosOp.smartFuel 0 .none (.blockOp .equal)
  [cons 2 [c 3, cons 4 [c 5]], .var .none 5]).isSome

#guard ClosOp.smartFuel 0 .none (.blockOp .equal)
    [cons 2 [c 3, cons 4 [c 5]], .var .none 5] ==
  ClosOp.smartFuel 100 .none (.blockOp .equal)
    [cons 2 [c 3, cons 4 [c 5]], .var .none 5]

#guard ClosOp.smartFuel 0 .none (.blockOp .equal)
    [.var .none 5, cons 2 [c 3, cons 4 [c 5]]] ==
  ClosOp.smartFuel 100 .none (.blockOp .equal)
    [.var .none 5, cons 2 [c 3, cons 4 [c 5]]]

end Flapjack.Test.ClosOpParity
