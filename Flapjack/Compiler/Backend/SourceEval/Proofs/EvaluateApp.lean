import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateEval

/-! Application cases in source evaluator oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- The ordinary primitive-operation subcase of the original application
induction case. The other operation classes are separate evaluator cases. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_AppSimple {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_preserves : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp) (opClass : getOpClass op = .simple)
    (argsIH : ExpsOracleAdjustedAt ci f compile state env args.reverse)
    (result : Result (List Value) Value)
    (source : evaluate state env [.app op args] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.app op args] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  let adjusted := { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
  simp only [evaluate, (fixClockEvaluate state env args.reverse []).1] at source
  change isInsertOracle ci f next.evalState ∧
    evaluate adjusted env [.app op args] =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)
  simp only [evaluate, (fixClockEvaluate adjusted env args.reverse []).1]
  cases argsRun : evaluate state env args.reverse with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [argsRun] using source
      have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.err error) argsRun inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.val values) argsRun inserted (by simp)
      cases app : doApp (middle.refs, middle.ffi) op values.reverse with
      | none =>
        simp [argsRun, opClass, app, typeError] at source
        obtain ⟨_, rfl⟩ := source
        exact (safe rfl).elim
      | some output =>
        obtain ⟨⟨refs, ffi⟩, appResult⟩ := output
        have pair : ({ middle with refs, ffi }, listResult appResult) = (next, result) := by
          simpa [argsRun, opClass, app] using source
        cases pair
        refine ⟨middleInserted, ?_⟩
        simp [adjusted, replacement, opClass, app]

/-- Function-application subcase of the original evaluator induction. The
body induction hypothesis is required only for an actual call with a nonzero
clock, at its decremented-clock input. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_AppFunction {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_preserves : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (opClass : getOpClass op = .funApp) (argsIH : ExpsOracleAdjustedAt ci f compile state env args.reverse)
    (bodyIH : ∀ (middle : State F) (values : List Value) (callEnv : SemEnv Value) (body : AstHOL.Exp),
      evaluate state env args.reverse = (middle, .val values) →
      doOpApp values.reverse = some (callEnv, body) → middle.clock ≠ 0 →
      ExpsOracleAdjustedAt ci f compile (decClock middle) callEnv [body])
    (result : Result (List Value) Value) (source : evaluate state env [.app op args] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.app op args] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  let adjusted := { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
  simp only [evaluate, (fixClockEvaluate state env args.reverse []).1] at source
  change isInsertOracle ci f next.evalState ∧
    evaluate adjusted env [.app op args] =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)
  simp only [evaluate, (fixClockEvaluate adjusted env args.reverse []).1]
  cases argsRun : evaluate state env args.reverse with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [argsRun] using source
      have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.err error) argsRun inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.val values) argsRun inserted (by simp)
      cases app : doOpApp values.reverse with
      | none =>
        simp [argsRun, opClass, app, typeError] at source
        obtain ⟨_, rfl⟩ := source
        exact (safe rfl).elim
      | some call =>
        obtain ⟨callEnv, body⟩ := call
        by_cases clock : middle.clock = 0
        · simp [argsRun, opClass, app, clock, timeoutError] at source
          obtain ⟨rfl, rfl⟩ := source
          exact ⟨middleInserted, by simp [adjusted, replacement, opClass, app, clock, timeoutError]⟩
        · have bodyRun : evaluate (decClock middle) callEnv [body] = (next, result) := by
            simpa [argsRun, opClass, app, clock] using source
          obtain ⟨nextInserted, bodyReplacement⟩ :=
            bodyIH middle values callEnv body argsRun app clock next result bodyRun (by simpa [decClock] using middleInserted) safe
          exact ⟨nextInserted, by simpa [adjusted, replacement, opClass, app, clock, decClock] using bodyReplacement⟩

/-- Thunk-forcing subcase of the original application induction. Its body
induction hypothesis is needed only for an actual unevaluated thunk call at a
nonzero clock. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_AppForce {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_preserves : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (opClass : getOpClass op = .force) (argsIH : ExpsOracleAdjustedAt ci f compile state env args.reverse)
    (bodyIH : ∀ (middle : State F) (values : List Value) (thunk : Value)
      (callEnv : SemEnv Value) (body : AstHOL.Exp),
      evaluate state env args.reverse = (middle, .val values) →
      destThunk values.reverse middle.refs = .isThunk .notEvaluated thunk →
      doOpApp [thunk, .conv none []] = some (callEnv, body) → middle.clock ≠ 0 →
      ExpsOracleAdjustedAt ci f compile (decClock middle) callEnv [body])
    (result : Result (List Value) Value) (source : evaluate state env [.app op args] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.app op args] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  let adjusted := { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
  simp only [evaluate, (fixClockEvaluate state env args.reverse []).1] at source
  change isInsertOracle ci f next.evalState ∧
    evaluate adjusted env [.app op args] =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)
  simp only [evaluate, (fixClockEvaluate adjusted env args.reverse []).1]
  cases argsRun : evaluate state env args.reverse with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [argsRun] using source
      have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.err error) argsRun inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.val values) argsRun inserted (by simp)
      cases thunkRun : destThunk values.reverse middle.refs with
      | badRef | notThunk =>
        simp [argsRun, opClass, thunkRun, typeError] at source
        obtain ⟨_, rfl⟩ := source
        exact (safe rfl).elim
      | isThunk mode thunk =>
        cases mode with
        | evaluated =>
          have pair : (middle, .val [thunk]) = (next, result) := by
            simpa [argsRun, opClass, thunkRun] using source
          cases pair
          exact ⟨middleInserted, by simp [adjusted, replacement, opClass, thunkRun]⟩
        | notEvaluated =>
          cases app : doOpApp [thunk, .conv none []] with
          | none =>
            simp [argsRun, opClass, thunkRun, app, typeError] at source
            obtain ⟨_, rfl⟩ := source
            exact (safe rfl).elim
          | some call =>
            obtain ⟨callEnv, body⟩ := call
            by_cases clock : middle.clock = 0
            · simp [argsRun, opClass, thunkRun, app, clock, timeoutError] at source
              obtain ⟨rfl, rfl⟩ := source
              exact ⟨middleInserted, by simp [adjusted, replacement, opClass, thunkRun, app, clock, timeoutError]⟩
            · cases bodyRun : evaluate (decClock middle) callEnv [body] with
              | mk after bodyResult =>
                cases bodyResult with
                | err error =>
                  have pair : (after, .err error) = (next, result) := by
                    simpa [argsRun, opClass, thunkRun, app, clock, bodyRun] using source
                  have bodySafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
                    intro bad
                    apply safe
                    have h := congrArg Prod.snd pair
                    simpa [bad] using h.symm
                  obtain ⟨afterInserted, bodyReplacement⟩ :=
                    bodyIH middle values thunk callEnv body argsRun thunkRun app clock after (.err error) bodyRun
                      (by simpa [decClock] using middleInserted) bodySafe
                  simp only [decClock] at bodyReplacement
                  cases pair
                  exact ⟨afterInserted, by simp [adjusted, replacement, opClass, thunkRun, app, clock, decClock, bodyReplacement]⟩
                | val newValues =>
                  obtain ⟨afterInserted, bodyReplacement⟩ :=
                    bodyIH middle values thunk callEnv body argsRun thunkRun app clock after (.val newValues) bodyRun
                      (by simpa [decClock] using middleInserted) (by simp)
                  simp only [decClock] at bodyReplacement
                  cases updated : updateThunk values.reverse after.refs newValues with
                  | none =>
                    simp [argsRun, opClass, thunkRun, app, clock, bodyRun, updated, typeError] at source
                    obtain ⟨_, rfl⟩ := source
                    exact (safe rfl).elim
                  | some refs =>
                    have pair : ({ after with refs }, .val newValues) = (next, result) := by
                      simpa [argsRun, opClass, thunkRun, app, clock, bodyRun, updated] using source
                    cases pair
                    exact ⟨afterInserted, by simp [adjusted, replacement, opClass, thunkRun, app, clock, decClock, bodyReplacement, updated]⟩

/-- Only the Eval operator belongs to the evaluator's Eval operation class.
This Flapjack lemma follows from the source operation-class definition. -/
theorem opClass_eval_eq (op : Op) (h : getOpClass op = .evalOp) : op = .eval := by
  cases op <;> simp_all [getOpClass]
  case thunkOp thunk => cases thunk <;> simp_all

/-- The complete application-expression case, assembling all four operation
classes with the corresponding evaluator induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_App {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (preserves : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (argsIH : ExpsOracleAdjustedAt ci f compile state env args.reverse)
    (functionIH : getOpClass op = .funApp → ∀ (middle : State F) (values : List Value) (callEnv : SemEnv Value) (body : AstHOL.Exp),
      evaluate state env args.reverse = (middle, .val values) →
      doOpApp values.reverse = some (callEnv, body) → middle.clock ≠ 0 →
      ExpsOracleAdjustedAt ci f compile (decClock middle) callEnv [body])
    (forceIH : getOpClass op = .force → ∀ (middle : State F) (values : List Value) (thunk : Value)
      (callEnv : SemEnv Value) (body : AstHOL.Exp),
      evaluate state env args.reverse = (middle, .val values) →
      destThunk values.reverse middle.refs = .isThunk .notEvaluated thunk →
      doOpApp [thunk, .conv none []] = some (callEnv, body) → middle.clock ≠ 0 →
      ExpsOracleAdjustedAt ci f compile (decClock middle) callEnv [body])
    (evalIH : getOpClass op = .evalOp → ∀ (middle decoded : State F) (values : List Value) (evalEnv : SemEnv Value) (decs : List Dec),
      evaluate state env args.reverse = (middle, .val values) →
      doEvalRes (β := Value) values.reverse middle = (decoded, .val (evalEnv, decs)) →
      decoded.clock ≠ 0 → DecsOracleAdjustedAt ci f compile (decClock decoded) evalEnv decs)
    (result : Result (List Value) Value) (source : evaluate state env [.app op args] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.app op args] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  cases opClass : getOpClass op with
  | simple => exact adjustOracle_evaluate_AppSimple ci f compile preserves state next env op args opClass argsIH result source inserted safe
  | funApp => exact adjustOracle_evaluate_AppFunction ci f compile preserves state next env op args opClass argsIH (functionIH opClass) result source inserted safe
  | force => exact adjustOracle_evaluate_AppForce ci f compile preserves state next env op args opClass argsIH (forceIH opClass) result source inserted safe
  | evalOp =>
    have eq := opClass_eval_eq op opClass
    subst op
    exact adjustOracle_evaluate_Eval ci f compile preserves state next env args argsIH (evalIH rfl) result source inserted safe

end Flapjack.Compiler.Backend.SourceEval.Proofs
