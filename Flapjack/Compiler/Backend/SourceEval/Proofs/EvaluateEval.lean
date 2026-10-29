import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateControl

/-! Dynamic Eval dispatch in the source evaluator's oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Successful dynamic Eval dispatch under oracle adjustment. The callback may
return the compiled declarations or the original declarations; both paths
preserve the insertion invariant. This is Flapjack proof infrastructure
derived from the original `do_eval_adjust` lemma. -/
theorem doEvalRes_adjust_success {Config F β : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (values : List Value) (state decoded : State F)
    (env : SemEnv Value) (decs : List Dec)
    (success : doEvalRes (β := β) values state = (decoded, .val (env, decs)))
    (inserted : isInsertOracle ci f state.evalState) :
    isInsertOracle ci f decoded.evalState ∧
      (doEvalRes (β := β) values { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } =
        ({ decoded with evalState := adjustOracle ci (compile ∘ f) decoded.evalState }, .val (env, compile decs)) ∨
       doEvalRes (β := β) values { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } =
        ({ decoded with evalState := adjustOracle ci (compile ∘ f) decoded.evalState }, .val (env, decs))) := by
  cases run : doEval values state.evalState with
  | none => simp [doEvalRes, run] at success
  | some output =>
    obtain ⟨foundEnv, foundDecs, evalState⟩ := output
    simp [doEvalRes, run] at success
    obtain ⟨rfl, rfl, rfl⟩ := success
    obtain ⟨adjusted, nextInserted⟩ := doEval_adjust ci f compile values state.evalState foundEnv foundDecs evalState run inserted
    refine ⟨nextInserted, ?_⟩
    rcases adjusted with transformed | unchanged
    · left
      simp [doEvalRes, transformed]
    · right
      simp [doEvalRes, unchanged]

/-- The Eval callback can choose either declarations returned by the oracle or
their compiled form. If the original evaluation is safe, both choices give the
same adjusted evaluation. This Flapjack lemma combines the induction
hypothesis with the declaration compiler-preservation premise. -/
theorem evaluateDecs_adjusted_compiled {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile)
    (decs : List Dec) (state next : State F) (env : SemEnv Value)
    (ih : DecsOracleAdjustedAt ci f compile state env decs) (result : Result (SemEnv Value) Value)
    (run : evaluateDecs state env decs = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env decs =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env (compile decs) =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  obtain ⟨nextInserted, replacement⟩ := ih next result run inserted safe
  exact ⟨nextInserted, replacement, preserves _ _ env decs result replacement safe⟩

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

/-- Oracle adjustment commutes with Eval's final environment/error handling.
The insertion invariant for the evaluated declarations is retained unless the
result is a type error. This is Flapjack infrastructure for the Eval case. -/
theorem finishEval_adjust {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (before after next : State F) (env : SemEnv Value)
    (inner : Result (SemEnv Value) Value) (result : Result (List Value) Value)
    (run : finishEval before after env inner = (next, result))
    (inserted : isInsertOracle ci f after.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      finishEval { before with evalState := adjustOracle ci (compile ∘ f) before.evalState }
        { after with evalState := adjustOracle ci (compile ∘ f) after.evalState } env inner =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  cases inner with
  | err error =>
    cases error with
    | abort abort =>
      simp [finishEval] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨inserted, by simp [finishEval]⟩
    | raise value =>
      simp [finishEval] at run
      obtain ⟨rfl, rfl⟩ := run
      constructor
      · simpa only [isInsert_reset] using inserted
      · simp [finishEval, adjustOracle_reset]
  | val newEnv =>
    cases declared : declareEnv after.evalState (extendDecEnv newEnv env) with
    | none =>
      simp [finishEval, declared, typeError] at run
      obtain ⟨_, rfl⟩ := run
      exact (safe rfl).elim
    | some pair =>
      obtain ⟨value, evalState⟩ := pair
      simp [finishEval, declared] at run
      obtain ⟨rfl, rfl⟩ := run
      have evalInserted := declareEnv_isInsert ci f _ (extendDecEnv newEnv env) value evalState declared inserted
      constructor
      · simpa only [isInsert_reset] using evalInserted
      · simp [finishEval, declareEnv_adjust, declared, adjustOracle_reset]

/-- Eval continuation after successful decoding, with the evaluator's
clock clamp removed using `fixClockEvaluate`. This factorization is Flapjack
proof infrastructure and has no separate HOL declaration. -/
noncomputable def continueEval {F : Type} (before decoded : State F) (env : SemEnv Value)
    (decs : List Dec) : State F × Result (List Value) Value :=
  if decoded.clock = 0 then timeoutError decoded else
    let evaluated := evaluateDecs (decClock decoded) env decs
    finishEval before evaluated.1 env evaluated.2

/-- Once Eval has decoded its declarations, both possible adjusted callback
outputs lead to the same observable state and result. This is Flapjack proof
infrastructure, conditional only on the corresponding declaration induction
hypothesis and original compiler-preservation premise. -/
theorem continueEval_adjust {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile)
    (before decoded next : State F) (env : SemEnv Value) (decs : List Dec)
    (ih : decoded.clock ≠ 0 → DecsOracleAdjustedAt ci f compile (decClock decoded) env decs)
    (result : Result (List Value) Value) (run : continueEval before decoded env decs = (next, result))
    (inserted : isInsertOracle ci f decoded.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      continueEval { before with evalState := adjustOracle ci (compile ∘ f) before.evalState }
        { decoded with evalState := adjustOracle ci (compile ∘ f) decoded.evalState } env decs =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) ∧
      continueEval { before with evalState := adjustOracle ci (compile ∘ f) before.evalState }
        { decoded with evalState := adjustOracle ci (compile ∘ f) decoded.evalState } env (compile decs) =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  by_cases clock : decoded.clock = 0
  · simp [continueEval, clock, timeoutError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨inserted, by simp [continueEval, clock, timeoutError], by simp [continueEval, clock, timeoutError]⟩
  · cases evaluated : evaluateDecs (decClock decoded) env decs with
    | mk after inner =>
      have innerSafe : inner ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd run
        simpa [continueEval, clock, evaluated, bad, finishEval] using h.symm
      have sourceFinish : finishEval before after env inner = (next, result) := by
        simpa [continueEval, clock, evaluated] using run
      obtain ⟨afterInserted, original, compiled⟩ :=
        evaluateDecs_adjusted_compiled ci f compile preserves decs (decClock decoded) after env (ih clock) inner
          evaluated (by simpa [decClock] using inserted) innerSafe
      simp only [decClock] at original compiled
      obtain ⟨nextInserted, finish⟩ := finishEval_adjust ci f compile before after next env inner result sourceFinish afterInserted safe
      refine ⟨nextInserted, ?_, ?_⟩
      · simpa [continueEval, clock, decClock, original] using finish
      · simpa [continueEval, clock, decClock, compiled] using finish

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

/-- Successful dynamic Eval branch, composed against the actual evaluator.
This Flapjack lemma is a case-building step: it still takes the successful
argument and decoder runs as premises. Its declaration induction hypothesis is
restricted to the actual decremented-clock state. It is not the full HOL
induction case. -/
theorem evaluate_eval_adjust_success {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile)
    (state middle decoded next : State F) (env evalEnv : SemEnv Value)
    (args : List AstHOL.Exp) (values : List Value) (decs : List Dec)
    (argsIH : ExpsOracleAdjustedAt ci f compile state env args.reverse)
    (decsIH : decoded.clock ≠ 0 → DecsOracleAdjustedAt ci f compile (decClock decoded) evalEnv decs)
    (argsRun : evaluate state env args.reverse = (middle, .val values))
    (decodedRun : doEvalRes (β := Value) values.reverse middle = (decoded, .val (evalEnv, decs)))
    (result : Result (List Value) Value) (run : evaluate state env [.app .eval args] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.app .eval args] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  obtain ⟨middleInserted, adjustedArgs⟩ := argsIH middle (.val values) argsRun inserted (by simp)
  obtain ⟨decodedInserted, adjustedDecode⟩ :=
    doEvalRes_adjust_success ci f compile values.reverse middle decoded evalEnv decs decodedRun middleInserted
  have continuation : continueEval middle decoded evalEnv decs = (next, result) := by
    rw [← evaluate_eval_success state middle decoded env evalEnv args values decs argsRun decodedRun]
    exact run
  obtain ⟨nextInserted, original, compiled⟩ :=
    continueEval_adjust ci f compile preserves middle decoded next evalEnv decs decsIH result continuation decodedInserted safe
  refine ⟨nextInserted, ?_⟩
  rcases adjustedDecode with transformed | unchanged
  · rw [evaluate_eval_success _ _ _ env evalEnv args values (compile decs) adjustedArgs transformed]
    exact compiled
  · rw [evaluate_eval_success _ _ _ env evalEnv args values decs adjustedArgs unchanged]
    exact original

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

/-- Dynamic Eval application case of the original evaluator induction. The
declaration induction hypothesis applies only to the decoded declarations at
the actual decremented-clock state, when decoding succeeds and the clock is
nonzero. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Eval {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (args : List AstHOL.Exp)
    (argsIH : ExpsOracleAdjustedAt ci f compile state env args.reverse)
    (decsIH : ∀ (middle decoded : State F) (values : List Value) (evalEnv : SemEnv Value) (decs : List Dec),
      evaluate state env args.reverse = (middle, .val values) →
      doEvalRes (β := Value) values.reverse middle = (decoded, .val (evalEnv, decs)) →
      decoded.clock ≠ 0 → DecsOracleAdjustedAt ci f compile (decClock decoded) evalEnv decs)
    (result : Result (List Value) Value) (source : evaluate state env [.app .eval args] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.app .eval args] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  cases argsRun : evaluate state env args.reverse with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by
        rw [evaluate_eval_args_error state middle env args error argsRun] at source
        exact source
      have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, adjustedArgs⟩ := argsIH middle (.err error) argsRun inserted innerSafe
      cases pair
      exact ⟨middleInserted, evaluate_eval_args_error _ _ env args error adjustedArgs⟩
    | val values =>
      cases decoded : doEval values.reverse middle.evalState with
      | none =>
        have failed := evaluate_eval_decode_failure state middle env args values argsRun decoded
        rw [failed] at source
        have h := congrArg Prod.snd source
        apply False.elim
        apply safe
        exact h.symm
      | some output =>
        obtain ⟨evalEnv, decs, evalState⟩ := output
        have decodedRun : doEvalRes (β := Value) values.reverse middle =
            ({ middle with evalState }, .val (evalEnv, decs)) := by simp [doEvalRes, decoded]
        exact evaluate_eval_adjust_success ci f compile preserves state middle { middle with evalState } next
          env evalEnv args values decs argsIH (decsIH middle _ values evalEnv decs argsRun decodedRun)
          argsRun decodedRun result source inserted safe

end Flapjack.Compiler.Backend.SourceEval.Proofs
