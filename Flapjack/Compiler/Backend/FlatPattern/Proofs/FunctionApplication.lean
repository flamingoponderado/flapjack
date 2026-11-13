module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.ExpressionList

@[expose] public section

/-! Function application for the flat pattern compiler. The evaluator and
proof-side value/state relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- An argument-evaluation error propagates through an application. -/
theorem evaluate_app_args_error {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (op : FlatLang.Op)
    (args : List FlatLang.Exp) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .err error)) :
    FlatSem.evaluate env state [.app trace op args] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock]

/-- A function application with invalid operands fails with a type error. -/
theorem evaluate_call_bad {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (values : List FlatSem.Value)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values))
    (call : FlatSem.doOpApp values.reverse = none) :
    FlatSem.evaluate env state [.app trace (.src .opapp) args] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, call]

/-- A valid function call at zero clock times out before entering its body. -/
theorem evaluate_call_timeout {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (values : List FlatSem.Value) (callEnv : FlatSem.Environment FlatSem.Value) (body : FlatLang.Exp)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values))
    (call : FlatSem.doOpApp values.reverse = some (callEnv, body))
    (zero : min state.clock next.clock = 0) :
    FlatSem.evaluate env state [.app trace (.src .opapp) args] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .timeoutError)) := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, call, zero]

/-- A valid function call with remaining clock evaluates its selected body. -/
theorem evaluate_call_body {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (values : List FlatSem.Value) (callEnv : FlatSem.Environment FlatSem.Value) (body : FlatLang.Exp)
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values))
    (call : FlatSem.doOpApp values.reverse = some (callEnv, body))
    (positive : min state.clock next.clock ≠ 0) :
    FlatSem.evaluate env state [.app trace (.src .opapp) args] =
      FlatSem.evaluate callEnv (FlatSem.decClock { next with clock := min state.clock next.clock }) [body] := by
  simp [FlatSem.evaluate, argsRun, FlatSem.fixClock, call, positive]

end Flapjack.Compiler.Backend.FlatPattern
