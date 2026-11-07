import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateControl
import Flapjack.EvaluateHOL.EvalDispatch

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
    obtain ⟨adjusted, nextInserted⟩ := doEval_adjust values state.evalState foundEnv foundDecs evalState ci f compile ⟨run, inserted⟩
    refine ⟨nextInserted, ?_⟩
    rcases adjusted with transformed | unchanged
    · left
      simp [doEvalRes, transformed]
    · right
      simp [doEvalRes, unchanged]

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
      have evalInserted := declareEnv_isInsert _ (extendDecEnv newEnv env) value evalState ci f ⟨declared, inserted⟩
      constructor
      · simpa only [isInsert_reset] using evalInserted
      · simp [finishEval, declareEnv_adjust, declared, adjustOracle_reset]

/-- Once Eval has decoded its declarations, both possible adjusted callback
outputs lead to the same observable state and result. This is Flapjack proof
infrastructure, conditional only on the corresponding declaration induction
hypothesis and original compiler-preservation premise. -/
theorem continueEval_adjust {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (before decoded next : State F) (env : SemEnv Value) (decs : List Dec)
    (ih : decoded.clock ≠ 0 → DecsOracleAdjustedAt compile ci f (decClock decoded) env decs)
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
      obtain ⟨afterInserted, original⟩ :=
        ih clock after inner ⟨evaluated, (by simpa [decClock] using inserted), innerSafe⟩
      have compiled := preserves _ env decs _ inner ⟨original, innerSafe⟩
      simp only [decClock] at original compiled
      obtain ⟨nextInserted, finish⟩ := finishEval_adjust ci f compile before after next env inner result sourceFinish afterInserted safe
      refine ⟨nextInserted, ?_, ?_⟩
      · simpa [continueEval, clock, decClock, original] using finish
      · simpa [continueEval, clock, decClock, compiled] using finish

/-- Successful dynamic Eval branch, composed against the actual evaluator.
This Flapjack lemma is a case-building step: it still takes the successful
argument and decoder runs as premises. Its declaration induction hypothesis is
restricted to the actual decremented-clock state. It is not the full HOL
induction case. -/
theorem evaluate_eval_adjust_success {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state middle decoded next : State F) (env evalEnv : SemEnv Value)
    (args : List AstHOL.Exp) (values : List Value) (decs : List Dec)
    (argsIH : ExpsOracleAdjustedAt compile ci f state env args.reverse)
    (decsIH : decoded.clock ≠ 0 → DecsOracleAdjustedAt compile ci f (decClock decoded) evalEnv decs)
    (argsRun : evaluate state env args.reverse = (middle, .val values))
    (decodedRun : doEvalRes (β := Value) values.reverse middle = (decoded, .val (evalEnv, decs)))
    (result : Result (List Value) Value) (run : evaluate state env [.app .eval args] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.app .eval args] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  obtain ⟨middleInserted, adjustedArgs⟩ := argsIH middle (.val values) ⟨argsRun, inserted, (by simp)⟩
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

/-- Flapjack proof infrastructure for the dynamic Eval branch of HOL's
application induction case, using the decoded declarations at the actual
decremented-clock state. -/
theorem adjustOracle_evaluate_Eval {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state next : State F) (env : SemEnv Value) (args : List AstHOL.Exp)
    (argsIH : ExpsOracleAdjustedAt compile ci f state env args.reverse)
    (decsIH : ∀ (middle decoded : State F) (values : List Value) (evalEnv : SemEnv Value) (decs : List Dec),
      evaluate state env args.reverse = (middle, .val values) →
      doEvalRes (β := Value) values.reverse middle = (decoded, .val (evalEnv, decs)) →
      decoded.clock ≠ 0 → DecsOracleAdjustedAt compile ci f (decClock decoded) evalEnv decs)
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
      obtain ⟨middleInserted, adjustedArgs⟩ := argsIH middle (.err error) ⟨argsRun, inserted, innerSafe⟩
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
