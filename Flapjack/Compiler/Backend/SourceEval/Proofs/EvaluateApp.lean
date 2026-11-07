import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateEval

/-! Application cases in source evaluator oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Flapjack proof infrastructure for the ordinary primitive-operation branch
of HOL's application induction case; HOL has no separate Simple case. -/
theorem adjustOracle_evaluate_AppSimple {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state next : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp) (opClass : getOpClass op = .simple)
    (argsIH : ExpsOracleAdjustedAt compile ci f state env args.reverse)
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
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.err error) ⟨argsRun, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.val values) ⟨argsRun, inserted, (by simp)⟩
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

/-- Flapjack proof infrastructure for the function-application branch of HOL's
application induction case, using the decremented-clock body hypothesis. -/
theorem adjustOracle_evaluate_AppFunction {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state next : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (opClass : getOpClass op = .funApp) (argsIH : ExpsOracleAdjustedAt compile ci f state env args.reverse)
    (bodyIH : ∀ (middle : State F) (values : List Value) (callEnv : SemEnv Value) (body : AstHOL.Exp),
      evaluate state env args.reverse = (middle, .val values) →
      doOpApp values.reverse = some (callEnv, body) → middle.clock ≠ 0 →
      ExpsOracleAdjustedAt compile ci f (decClock middle) callEnv [body])
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
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.err error) ⟨argsRun, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.val values) ⟨argsRun, inserted, (by simp)⟩
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
            bodyIH middle values callEnv body argsRun app clock next result ⟨bodyRun, (by simpa [decClock] using middleInserted), safe⟩
          exact ⟨nextInserted, by simpa [adjusted, replacement, opClass, app, clock, decClock] using bodyReplacement⟩

/-- Flapjack proof infrastructure for the thunk-forcing branch of HOL's
application induction case, using the decremented-clock body hypothesis. -/
theorem adjustOracle_evaluate_AppForce {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state next : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (opClass : getOpClass op = .force) (argsIH : ExpsOracleAdjustedAt compile ci f state env args.reverse)
    (bodyIH : ∀ (middle : State F) (values : List Value) (thunk : Value)
      (callEnv : SemEnv Value) (body : AstHOL.Exp),
      evaluate state env args.reverse = (middle, .val values) →
      destThunk values.reverse middle.refs = .isThunk .notEvaluated thunk →
      doOpApp [thunk, .conv none []] = some (callEnv, body) → middle.clock ≠ 0 →
      ExpsOracleAdjustedAt compile ci f (decClock middle) callEnv [body])
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
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.err error) ⟨argsRun, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := argsIH middle (.val values) ⟨argsRun, inserted, (by simp)⟩
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
                    bodyIH middle values thunk callEnv body argsRun thunkRun app clock after (.err error) ⟨bodyRun,
                      (by simpa [decClock] using middleInserted), bodySafe⟩
                  simp only [decClock] at bodyReplacement
                  cases pair
                  exact ⟨afterInserted, by simp [adjusted, replacement, opClass, thunkRun, app, clock, decClock, bodyReplacement]⟩
                | val newValues =>
                  obtain ⟨afterInserted, bodyReplacement⟩ :=
                    bodyIH middle values thunk callEnv body argsRun thunkRun app clock after (.val newValues) ⟨bodyRun,
                      (by simpa [decClock] using middleInserted), (by simp)⟩
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

/-- The application clause of the evaluator induction, retaining its four
original hypotheses. Evaluation inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_App {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (ih :
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (pair : SemEnv Value × Flapjack.AstHOL.Exp) (callEnv : SemEnv Value) (body : Flapjack.AstHOL.Exp),
        evaluate state env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .funApp ∧ doOpApp values.reverse = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → ExpsOracleAdjustedAt compile ci f (decClock middle) callEnv [body]) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (decoded : State F) (decodedResult : Result (SemEnv Value × List Dec) Value)
          (pair : SemEnv Value × List Dec) (evalEnv : SemEnv Value) (decs : List Dec),
        evaluate state env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .evalOp ∧ doEvalRes values.reverse middle = (decoded, decodedResult) ∧
        decodedResult = .val pair ∧ pair = (evalEnv, decs) ∧ decoded.clock ≠ 0 →
        DecsOracleAdjustedAt compile ci f (decClock decoded) evalEnv decs) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (mode : ThunkMode) (thunk : Value) (pair : SemEnv Value × Flapjack.AstHOL.Exp)
          (callEnv : SemEnv Value) (body : Flapjack.AstHOL.Exp),
        evaluate state env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .force ∧ destThunk values.reverse middle.refs = .isThunk mode thunk ∧
        mode = .notEvaluated ∧ doOpApp [thunk, .conv none []] = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → ExpsOracleAdjustedAt compile ci f (decClock middle) callEnv [body]) ∧
      ExpsOracleAdjustedAt compile ci f state env args.reverse) :
    ExpsOracleAdjustedAt compile ci f state env [.app op args] := by
  obtain ⟨functionIH, evalIH, forceIH, argsIH⟩ := ih
  intro next result ⟨source, inserted, safe⟩
  cases opClass : getOpClass op with
  | simple => exact adjustOracle_evaluate_AppSimple ci f compile preserves state next env op args opClass argsIH result source inserted safe
  | funApp =>
    exact adjustOracle_evaluate_AppFunction ci f compile preserves state next env op args opClass argsIH
      (fun middle values callEnv body run app nonzero =>
        functionIH middle (.val values) values (callEnv, body) callEnv body ⟨run, rfl, opClass, app, rfl, nonzero⟩)
      result source inserted safe
  | force =>
    exact adjustOracle_evaluate_AppForce ci f compile preserves state next env op args opClass argsIH
      (fun middle values thunk callEnv body run thunkRun app nonzero =>
        forceIH middle (.val values) values .notEvaluated thunk (callEnv, body) callEnv body
          ⟨run, rfl, opClass, thunkRun, rfl, app, rfl, nonzero⟩)
      result source inserted safe
  | evalOp =>
    have eq : op = .eval := by
      cases op <;> simp_all [getOpClass]
      case thunkOp thunk => cases thunk <;> simp_all
    subst op
    exact adjustOracle_evaluate_Eval ci f compile preserves state next env args argsIH
      (fun middle decoded values evalEnv decs run decodedRun nonzero =>
        evalIH middle (.val values) values decoded (.val (evalEnv, decs)) (evalEnv, decs) evalEnv decs
          ⟨run, rfl, rfl, decodedRun, rfl, rfl, nonzero⟩)
      result source inserted safe

end Flapjack.Compiler.Backend.SourceEval.Proofs
