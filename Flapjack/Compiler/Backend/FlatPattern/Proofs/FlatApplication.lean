import Flapjack.Compiler.Backend.FlatPattern.Proofs.FunctionApplication
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PrimitiveGlobals

/-! Flat-primitive application in the proof-side pattern simulation. The
evaluator and relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A flat-specific application dispatches its evaluated, reversed arguments
to the primitive evaluator after clamping the clock. -/
theorem evaluate_flatApp_values {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (op : FlatLang.Op)
    (args : List FlatLang.Exp) (values : List FlatSem.Value)
    (notSource : ∀ sourceOp, op ≠ .src sourceOp)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values)) :
    FlatSem.evaluate env state [.app trace op args] =
      FlatSem.applyResult { next with clock := min state.clock next.clock } op values.reverse := by
  cases op with
  | src sourceOp => exact (notSource sourceOp rfl).elim
  | globalVarAlloc _ | globalVarInit _ | globalVarLookup _ | tagLenEq _ _ | lenEq _ | el _ | id =>
    simp [FlatSem.evaluate, FlatSem.fixClock, argsRun]

end Flapjack.Compiler.Backend.FlatPattern
