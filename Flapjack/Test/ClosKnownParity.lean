import Flapjack.Compiler.Backend.ClosKnown.Compile

/-! Replay approximation and compilation rows captured from pinned HOL. -/
namespace Flapjack.Test.ClosKnownParity
open Flapjack.Compiler.Backend ClosKnown
open Flapjack.Basis.Pure.MlString

private def f : ClosLang.Exp := .var .none 0
private def h : ClosLang.Exp := .var .none 1

#guard match [(ValApprox.clos 4 1 f 1, ValApprox.clos 4 1 f 1),
    (.clos 4 1 f 1, .clos 4 1 h 1),
    (.tuple 2 [.int 3, .impossible], .tuple 2 [.int 3, .int 5]),
    (.tuple 2 [.int 3], .tuple 3 [.int 3])].mapM (fun (x, y) => mergeFuel 100 x y) with
  | some [.clos 4 1 (.var .none 0) 1, .other, .tuple 2 [.int 3, .int 5], .other] => true
  | _ => false

#guard match (do
    let (a, g) ← knownOpFuel 100 (.globOp (.setGlobal 2)) [.int 5] .ln
    let (b, g) ← knownOpFuel 100 (.globOp (.global 2)) [] g
    let (c, g) ← knownOpFuel 100 (.memOp .el) [.tuple 0 [.int 8, .int 9], .int 1] g
    pure (a, b, c, sptToAList g)) with
  | some (.other, .int 5, .int 9, [(2, .int 5)]) => true
  | _ => false

private def fn : ClosLang.Exp := .fn (ofString "f") (some 4) none 1 (.var .none 0)
private def input : List ClosLang.Exp :=
  [.let .none [fn] (.app .none none (.var .none 0) [.op .none (.intOp (.const 42)) []]),
   .op .none (.globOp (.setGlobal 2)) [.op .none (.intOp (.const 5)) []],
   .op .none (.globOp (.global 2)) []]

#guard match compileFuel 100 (some (mkConfig 8 2)) input with
  | some (some config,
      [.let .none [.fn name (some 4) none 1 (.var .none 0)]
        (.let .none [.op .none (.intOp (.const 42)) []] (.var .none 0)),
       .op .none (.globOp (.setGlobal 2)) [.op .none (.intOp (.const 5)) []],
       .op .none (.intOp (.const 5)) []]) =>
       decide (name = ofString "f") && match sptToAList config.valApproxSpt with
       | [(2, .int 5)] => true
       | _ => false
  | _ => false

end Flapjack.Test.ClosKnownParity
