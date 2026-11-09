import Flapjack.Compiler.Backend.ClosFvs
import Flapjack.Compiler.Backend.ClosTicks
import Flapjack.Compiler.Backend.ClosLetop
import Flapjack.Compiler.Backend.ClosKnown.Inline

/-! Replay `clos_known_helpers_probe.out` from pinned HOL. -/
namespace Flapjack.Test.ClosKnownHelpersParity
open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString

#guard match [
    ClosLang.Exp.let .none [.var .none 0] (.fn (ofString "f") (some 4) (some [0, 1]) 1 (.var .none 3)),
    .letrec [ofString "f"] (some 4) (some [0]) [(1, .var .none 3)] (.var .none 1)
  ].mapM (ClosFvs.removeFuel 100 0) with
  | some [.let .none [.op .none (.memOp .el) []] (.fn name (some 4) (some [0, 1]) 1 (.op .none (.memOp .el) [])),
      .letrec names (some 4) (some [0]) [(1, .op .none (.memOp .el) [])] (.op .none (.memOp .el) [])] =>
      decide (name = ofString "f") && decide (names = [ofString "f"])
  | _ => false
#guard match [ClosLang.Exp.tick .none (.call .none 7 4 [.tick .none (.var .none 0)]),
    .fn (ofString "f") (some 4) none 1 (.tick .none (.var .none 0))].mapM (ClosTicks.removeFuel 100) with
  | some [.call .none 0 4 [.var .none 0], .fn name (some 4) none 1 (.var .none 0)] => decide (name = ofString "f")
  | _ => false
#guard match ClosLetop.compileFuel 100 (.let (.sourceLoc 1 2 3 4) [.var .none 2, .var .none 3]
    (.op .none (.intOp .add) [.var .none 0, .var .none 1])) with
  | some (.op (.sourceLoc 1 2 3 4) (.intOp .add) [.var .none 2, .var .none 3]) => true
  | _ => false

private def body : ClosLang.Exp := .op .none (.intOp .add) [.var .none 0, .var .none 0]
private def config : ClosKnown.Config := ClosKnown.mkConfig 8 2
#guard match ClosKnown.closApproxFuel 100 3 4 1 body, ClosKnown.closApproxFuel 100 2 4 1 body with
  | some (.clos 4 1 _ 3), some (.closNoInline 4 1) => true
  | _, _ => false
#guard match [
    (ClosKnown.ValApprox.clos 4 1 body 3, none), (.clos 4 1 body 4, none),
    (.closNoInline 4 1, none), (.clos 4 1 body 3, some 9),
    (.clos 4 1 (.var .none 1) 1, none),
    (.clos 4 1 (.fn (ofString "x") none none 1 (.var .none 0)) 1, none)
  ].mapM (fun (approx, loc) => ClosKnown.decideInlineFuel 100 config approx loc 1) with
  | some [.letInline (.op .none (.intOp .add) [.var .none 0, .var .none 0]),
      .annotate 4, .annotate 4, .nothing, .annotate 4, .annotate 4] => true
  | _ => false

end Flapjack.Test.ClosKnownHelpersParity
