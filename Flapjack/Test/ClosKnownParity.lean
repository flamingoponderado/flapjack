module

public import Flapjack.Compiler.Backend.ClosKnown.Compile

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.BackendCommon.Trace
public meta import Flapjack.Compiler.Backend.ClosKnown.Compile
public meta import Flapjack.Compiler.Backend.ClosKnown.Config
public meta import Flapjack.Compiler.Backend.ClosLang.Syntax
public meta import Flapjack.Misc.Sptree
@[expose] public section

/-! Replay approximation and compilation rows captured from pinned HOL. -/
namespace Flapjack.Test.ClosKnownParity
open Flapjack.Compiler.Backend ClosKnown
open Flapjack.Basis.Pure.MlString

private def f : ClosLang.Exp := .var .none 0
private def h : ClosLang.Exp := .var .none 1

#guard match [(ValApprox.clos 4 1 f 1, ValApprox.clos 4 1 f 1),
    (.clos 4 1 f 1, .clos 4 1 h 1),
    (.tuple 2 [.int 3, .impossible], .tuple 2 [.int 3, .int 5]),
    (.tuple 2 [.int 3], .tuple 3 [.int 3])].map (fun (x, y) => mergeHOL x y) with
  | [.clos 4 1 (.var .none 0) 1, .other, .tuple 2 [.int 3, .int 5], .other] => true
  | _ => false
#guard Id.run do
  let (a, g) := knownOpHOL (.globOp (.setGlobal 2)) [.int 5] .ln
  let (b, g) := knownOpHOL (.globOp (.global 2)) [] g
  let (c, g) := knownOpHOL (.memOp .el) [.tuple 0 [.int 8, .int 9], .int 1] g
  return match (a, b, c, sptToAList g) with
    | (.other, .int 5, .int 9, [(2, .int 5)]) => true
    | _ => false

-- `knownop_edges` also observes the exact update shape of a non-well-formed tree.
#guard Id.run do
  let g : Flapjack.Spt ValApprox := .bn .ln .ln
  let values := [
    (knownOpHOL (.globOp (.global 0)) [] g).1,
    (knownOpHOL (.globOp (.global 0)) [.int 4] (.ls (.int 6))).1,
    (knownOpHOL (.memOp .el) [.tuple 0 [.int 8], .int (-1)] g).1,
    (knownOpHOL (.memOp .el) [.tuple 0 [.int 8], .int 1] g).1,
    (knownOpHOL (.memOp .el) [.int 4, .impossible] g).1,
    (knownOpHOL (.memOp .el) [.tuple 0 [.int 8], .int 0, .other] g).1]
  let updated := (knownOpHOL (.globOp (.setGlobal 0)) [.int 7] g).2
  return match values, updated with
    | [.other, .other, .other, .other, .impossible, .other], .bs .ln (.int 7) .ln => true
    | _, _ => false

private def fn : ClosLang.Exp := .fn (ofString "f") (some 4) none 1 (.var .none 0)
private def input : List ClosLang.Exp :=
  [.let .none [fn] (.app .none none (.var .none 0) [.op .none (.intOp (.const 42)) []]),
   .op .none (.globOp (.setGlobal 2)) [.op .none (.intOp (.const 5)) []],
   .op .none (.globOp (.global 2)) []]

-- These three complete traversal results are captured as `known_inline`,
-- `known_letrec_globals`, and `known_impure_inline` in the original HOL probe.
#guard match knownListTotal (mkConfig 8 2) (input.take 1) [] .ln with
  | ([(.let .none [.fn name (some 4) none 1 (.var .none 0)]
       (.let .none [.op .none (.intOp (.const 42)) []] (.tick .none (.var .none 0))),
       .int 42)], .ln) => decide (name = ofString "f")
  | _ => false

#guard match knownListTotal (mkConfig 8 2)
    [.letrec [ofString "f"] (some 4) none
      [(0, .op .none (.globOp (.setGlobal 3)) [.op .none (.intOp (.const 7)) []])]
      (.op .none (.globOp (.global 3)) [])] [] .ln with
  | ([(.letrec [name] (some 4) none
       [(0, .op .none (.globOp (.setGlobal 3)) [.op .none (.intOp (.const 7)) []])]
       (.op .none (.globOp (.global 3)) []), .other)], .ln) => decide (name = ofString "f")
  | _ => false

#guard match knownListTotal (mkConfig 8 2)
    [.app .none none
      (.let .none [.op .none (.globOp (.setGlobal 2)) [.op .none (.intOp (.const 5)) []]] fn)
      [.op .none (.intOp (.const 42)) []]] [] .ln with
  | ([(.let .none [.op .none (.intOp (.const 42)) [],
       .let .none [.op .none (.globOp (.setGlobal 2)) [.op .none (.intOp (.const 5)) []]]
         (.fn name (some 4) none 1 (.var .none 0))]
       (.tick .none (.var .none 0)), .int 42)], .bn (.ls (.int 5)) .ln) =>
      decide (name = ofString "f")
  | _ => false

-- Zero initial fuel forces the production retry with inlining disabled.
-- A zero initial fuel also succeeds through an actual inlining decision.
#guard match knownListBounded 0 (mkConfig 8 2) (input.take 1) [] .ln with
  | some ([(.let _ [_] (.let _ [_] (.tick _ (.var _ 0))), .int 42)], .ln) => true
  | _ => false

#guard match knownListBounded 0 (mkConfig 8 0)
    [.op .none (.intOp (.const 5)) []] [] .ln with
  | some ([(.op .none (.intOp (.const 5)) [], .int 5)], .ln) => true
  | _ => false

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

-- The complete pass no longer fails on positive inlining at zero initial fuel.
#guard match compileFuel 0 (some (mkConfig 8 2)) input with
  | some (some _,
      [.let .none [.fn _ (some 4) none 1 (.var .none 0)]
        (.let .none [.op .none (.intOp (.const 42)) []] (.var .none 0)),
       .op .none (.globOp (.setGlobal 2)) [_],
       .op .none (.intOp (.const 5)) []]) => true
  | _ => false

end Flapjack.Test.ClosKnownParity
