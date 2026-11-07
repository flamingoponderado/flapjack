import Flapjack.EvaluateHOL.ClockFull

/-! Shared source-evaluator Eval-clause proof infrastructure. -/
namespace Flapjack.EvaluateHOL
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- The final environment and error handling of the Eval branch. This is a
Flapjack factorization of the corresponding evaluator clause, not a separate
HOL declaration. -/
def finishEval {F : Type} (before after : State F) (env : SemEnv Value)
    (result : Result (SemEnv Value) Value) : State F × Result (List Value) Value :=
  match result with
  | .val newEnv => match declareEnv after.evalState (extendDecEnv newEnv env) with
    | none => typeError after
    | some (value, evalState) =>
      ({ after with evalState := resetEnvGeneration before.evalState evalState }, .val [value])
  | .err (.abort err) => (after, .err (.abort err))
  | .err err =>
    ({ after with evalState := resetEnvGeneration before.evalState after.evalState }, .err err)

/-- Eval continuation after successful decoding, with the evaluator's
clock clamp removed using `fixClockEvaluate`. This factorization is Flapjack
proof infrastructure and has no separate HOL declaration. -/
noncomputable def continueEval {F : Type} (before decoded : State F) (env : SemEnv Value)
    (decs : List Dec) : State F × Result (List Value) Value :=
  if decoded.clock = 0 then timeoutError decoded else
    let evaluated := evaluateDecs (decClock decoded) env decs
    finishEval before evaluated.1 env evaluated.2

/-- The successful Eval-dispatch branch of the faithful evaluator is exactly
the factored continuation above. This Flapjack lemma connects the proof
infrastructure to the actual evaluator clause. -/
theorem evaluate_eval_success {F : Type} (state middle decoded : State F) (env evalEnv : SemEnv Value)
    (args : List AstHOL.Exp) (values : List Value) (decs : List Dec)
    (argsRun : evaluate state env args.reverse = (middle, .val values))
    (decodedRun : doEvalRes (β := Value) values.reverse middle = (decoded, .val (evalEnv, decs))) :
    evaluate state env [.app .eval args] = continueEval middle decoded evalEnv decs := by
  have fixedDecode : fixClock middle (doEvalRes (β := Value) values.reverse middle) =
      doEvalRes (β := Value) values.reverse middle := by
    apply fixClock_eq_of_bound
    simp [doEvalRes_clock]
  simp only [evaluate]
  rw [(fixClockEvaluate state env args.reverse []).1, argsRun]
  simp only [getOpClass]
  rw [fixedDecode, decodedRun]
  dsimp only
  by_cases clock : decoded.clock = 0
  · simp [clock, continueEval]
  · simp only [clock, if_false, (fixClockEvaluate (decClock decoded) evalEnv [] decs).2]
    cases run : evaluateDecs (decClock decoded) evalEnv decs with
    | mk after inner =>
      cases inner with
      | val newEnv =>
        cases h : declareEnv after.evalState (extendDecEnv newEnv evalEnv) <;>
          simp [run, continueEval, clock, finishEval, h]
        all_goals split <;> simp_all
      | err error =>
        cases error <;> simp [run, continueEval, clock, finishEval]

/-- Dynamic Eval propagates an error from evaluating its arguments. This
Flapjack helper unfolds the corresponding evaluator clause. -/
theorem evaluate_eval_args_error {F : Type} (state middle : State F) (env : SemEnv Value)
    (args : List AstHOL.Exp) (error : ErrorResult Value)
    (argsRun : evaluate state env args.reverse = (middle, .err error)) :
    evaluate state env [.app .eval args] = (middle, .err error) := by
  simp only [evaluate]
  rw [(fixClockEvaluate state env args.reverse []).1, argsRun]

/-- If dynamic Eval cannot decode its input, the evaluator reports a type
error. This Flapjack helper unfolds the corresponding evaluator clause. -/
theorem evaluate_eval_decode_failure {F : Type} (state middle : State F) (env : SemEnv Value)
    (args : List AstHOL.Exp) (values : List Value)
    (argsRun : evaluate state env args.reverse = (middle, .val values))
    (decodeFailure : doEval values.reverse middle.evalState = none) :
    evaluate state env [.app .eval args] = (middle, .err (.abort .typeError)) := by
  simp only [evaluate]
  rw [(fixClockEvaluate state env args.reverse []).1, argsRun]
  simp [getOpClass, doEvalRes, decodeFailure, fixClock]

/-- Source Eval follows successful operand evaluation, callback decoding,
declaration execution, and environment declaration, restoring the caller's
generation. This specialization is Flapjack proof infrastructure with no
separate HOL declaration. -/
theorem evaluate_sourceEval_success {F : Type}
    (env evalEnv newEnv : SemEnv Value) (state arguments last : SemanticPrimitivesHOL.State F)
    (exprs : List AstHOL.Exp) (values : List Value) (decs : List Dec)
    (begin after : Option EvalState) (value : Value)
    (operandRun : EvaluateHOL.evaluate state env exprs.reverse = (arguments, .val values.reverse))
    (decoded : SemanticPrimitivesHOL.doEval values arguments.evalState = some (evalEnv, decs, begin))
    (positive : 0 < arguments.clock)
    (declarationRun : EvaluateHOL.evaluateDecs
      (EvaluateHOL.decClock { arguments with evalState := begin }) evalEnv decs = (last, .val newEnv))
    (declared : declareEnv last.evalState (extendDecEnv newEnv evalEnv) = some (value, after)) :
    EvaluateHOL.evaluate state env [.app .eval exprs] =
      ({ last with evalState := resetEnvGeneration arguments.evalState after }, .val [value]) := by
  have result := evaluate_eval_success state arguments { arguments with evalState := begin } env evalEnv
    exprs values.reverse decs operandRun (by simp [doEvalRes, decoded])
  simpa [continueEval, finishEval, Nat.ne_of_gt positive, declarationRun, declared] using result

/-- A successful callback at clock zero returns timeout after installing the
source callback state. This specialization has no separate HOL declaration. -/
theorem evaluate_sourceEval_timeout {F : Type}
    (env evalEnv : SemEnv Value) (state arguments : SemanticPrimitivesHOL.State F)
    (exprs : List AstHOL.Exp) (values : List Value) (decs : List Dec) (begin : Option EvalState)
    (operandRun : EvaluateHOL.evaluate state env exprs.reverse = (arguments, .val values.reverse))
    (decoded : SemanticPrimitivesHOL.doEval values arguments.evalState = some (evalEnv, decs, begin))
    (zero : arguments.clock = 0) :
    EvaluateHOL.evaluate state env [.app .eval exprs] =
      ({ arguments with evalState := begin }, .err (.abort .timeoutError)) := by
  have result := evaluate_eval_success state arguments { arguments with evalState := begin } env evalEnv
    exprs values.reverse decs operandRun (by simp [doEvalRes, decoded])
  simpa [continueEval, zero, timeoutError] using result

/-- A declaration error propagates from source Eval. Raised exceptions reset
the generation, while aborts retain the declaration state. This specialization
has no separate HOL declaration. -/
theorem evaluate_sourceEval_declaration_error {F : Type}
    (env evalEnv : SemEnv Value) (state arguments last : SemanticPrimitivesHOL.State F)
    (exprs : List AstHOL.Exp) (values : List Value) (decs : List Dec)
    (begin : Option EvalState) (error : ErrorResult Value)
    (operandRun : EvaluateHOL.evaluate state env exprs.reverse = (arguments, .val values.reverse))
    (decoded : SemanticPrimitivesHOL.doEval values arguments.evalState = some (evalEnv, decs, begin))
    (positive : 0 < arguments.clock)
    (declarationRun : EvaluateHOL.evaluateDecs
      (EvaluateHOL.decClock { arguments with evalState := begin }) evalEnv decs = (last, .err error)) :
    EvaluateHOL.evaluate state env [.app .eval exprs] =
      (match error with
       | .abort _ => last
       | .raise _ => { last with evalState := resetEnvGeneration arguments.evalState last.evalState }, .err error) := by
  have result := evaluate_eval_success state arguments { arguments with evalState := begin } env evalEnv
    exprs values.reverse decs operandRun (by simp [doEvalRes, decoded])
  cases error <;> simpa [continueEval, finishEval, Nat.ne_of_gt positive, declarationRun] using result

end Flapjack.EvaluateHOL
