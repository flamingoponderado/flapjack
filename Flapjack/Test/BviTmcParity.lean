import Flapjack.Compiler.Backend.BviTmc
import Flapjack.Test.BviTmcOracle
import Flapjack.Compiler.Backend.BviInline
import Flapjack.Compiler.Backend.BviToData.Compile
import Flapjack.Compiler.Backend.DataToWord.Control
import Flapjack.Test.TmcProgramWordOracle

/-! Replay the complete original wrapper and worker examples. -/
namespace Flapjack.Test.BviTmcParity
open Flapjack.Compiler.Backend BviTmc

private def call : Bvi.Exp := .call 2 (some 3) [.var 0] none
private def cons (xs : List Bvi.Exp) : Bvi.Exp := .op (.blockOp (.cons 0)) xs
private def examples : List Bvi.Exp :=
  [cons [.var 0, call], cons [call, .var 0], cons [.var 0, cons [.var 0, call]],
   cons [call, .call 0 (some 7) [] none],
   .ifThenElse (.var 0) (cons [.var 0, call]) (.var 0),
   .let [.var 0] (cons [.var 1, call]),
   cons [call, call], cons [.call 0 (some 7) [] none, call],
   cons [call, .op (.intOp (.const 268435458)) []]]

#guard match examples.mapM (compileExpFuel 100 3 59 1) with
  | some results => Flapjack.Test.BviTmcOracle.matchesCaptured results
  | none => false

#guard match compileProgFuel 100 true 59 [(3, 1, cons [.var 0, call]), (7, 0, .var 0)] with
  | some (63, [(3, 1, .let [.var 0, .var 0]
       (.let [.op (.memOp (.mutCons 0 0)) [.var 0, .op (.intOp (.const 0)) []]]
         (.let [.call 2 (some 59) [.var 2, .var 0, .op (.intOp (.const 0)) []] none]
           (.op (.memOp .finaliseCons) [.var 1])))),
      (59, 3, .let [.var 0, .var 0]
       (.let [.op (.memOp (.mutCons 0 0)) [.var 0, .op (.intOp (.const 0)) []]]
         (.let [.op (.memOp .updateCons) [.var 0, .var 5, .var 4]]
           (.call 2 (some 59) [.var 3, .var 1, .op (.intOp (.const 0)) []] none)))),
      (7, 0, .var 0)]) => true
  | _ => false

#guard (compileExpFuel 0 3 59 1 (cons [.var 0, call])).isNone

private def wordConfig : DataToWord.Config :=
  ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩

#guard match (do
    let (_, code) ← compileProgFuel 100 true 59 [(3, 1, cons [.var 0, call]), (7, 0, .var 0)]
    let (_, code) ← BviInline.compileProgFuel 100 code
    let data ← code.mapM fun (loc, arity, body) => do
      pure (loc, arity, ← BviToData.compileExpFuel 100 arity body)
    data.mapM fun (loc, arity, body) => do
      let (body, _) ← DataToWord.compileControl? (width := 64) wordConfig loc 2 body
      pure (loc, arity + 1, body, 0)) with
  | some entries => Flapjack.Test.TmcProgramWordOracle.matchesCaptured entries
  | none => false

end Flapjack.Test.BviTmcParity
