module

public import Flapjack.EvaluateProps.NoEvalControl

@[expose] public section
namespace Flapjack.EvaluateProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
/-- The application induction case of evaluation without Eval state. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "eval_no_eval_simulation"]
theorem evalNoEval_App {F : Type} (es : Option EvalState)
    (s : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (ih :
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (pair : SemEnv Value × AstHOL.Exp) (callEnv : SemEnv Value) (body : AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .funApp ∧ doOpApp values.reverse = some pair ∧ pair = (callEnv, body) ∧
        middle.clock ≠ 0 → NoEvalExpsAt es (decClock middle) callEnv [body]) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (decoded : State F) (decodedResult : Result (SemEnv Value × List Dec) Value)
          (pair : SemEnv Value × List Dec) (evalEnv : SemEnv Value) (decs : List Dec),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .evalOp ∧ doEvalRes values.reverse middle = (decoded, decodedResult) ∧
        decodedResult = .val pair ∧ pair = (evalEnv, decs) ∧ decoded.clock ≠ 0 →
        NoEvalDecsAt es (decClock decoded) evalEnv decs) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (mode : ThunkMode) (thunk : Value) (pair : SemEnv Value × AstHOL.Exp)
          (callEnv : SemEnv Value) (body : AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .force ∧ destThunk values.reverse middle.refs = .isThunk mode thunk ∧
        mode = .notEvaluated ∧ doOpApp [thunk, .conv none []] = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → NoEvalExpsAt es (decClock middle) callEnv [body]) ∧
      NoEvalExpsAt es s env args.reverse) : NoEvalExpsAt es s env [.app op args] := by
  obtain ⟨callIH, evalIH, forceIH, argsIH⟩ := ih
  intro s' res ⟨run, absent, safe⟩
  rw [evaluate, (fixClockEvaluate s env args.reverse []).1] at run
  cases argsRun : evaluate s env args.reverse with
  | mk middle argResult =>
    cases argResult with
    | err error =>
      simp only [argsRun] at run
      cases run
      have target := argsIH s' (.err error) ⟨argsRun, absent, safe⟩
      refine ⟨target.1, ?_⟩
      rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, target.2]
    | val values =>
      simp only [argsRun] at run
      have targetArgs := argsIH middle (.val values) ⟨argsRun, absent, by simp⟩
      cases opClass : getOpClass op with
      | simple =>
        rw [opClass] at run
        cases app : doApp (middle.refs, middle.ffi) op values.reverse with
        | none =>
          simp [app, typeError] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
        | some output =>
          obtain ⟨⟨refs, ffi⟩, result⟩ := output
          simp only [app] at run
          cases run
          refine ⟨targetArgs.1, ?_⟩
          rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, targetArgs.2]
          simp [opClass, app]
      | funApp =>
        rw [opClass] at run
        cases app : doOpApp values.reverse with
        | none =>
          simp [app, typeError] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
        | some pair =>
          obtain ⟨callEnv, body⟩ := pair
          simp only [app] at run
          by_cases zero : middle.clock = 0
          · simp [zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨targetArgs.1, ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, targetArgs.2]
            simp [opClass, app, zero, timeoutError]
          · simp only [zero, ↓reduceIte] at run
            have targetCall := callIH middle (.val values) values (callEnv, body) callEnv body
              ⟨argsRun, rfl, opClass, app, rfl, zero⟩ s' res
              ⟨run, by simpa [decClock] using targetArgs.1, safe⟩
            refine ⟨targetCall.1, ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, targetArgs.2]
            simpa [opClass, app, decClock, zero] using targetCall.2
      | force =>
        rw [opClass] at run
        cases thunk : destThunk values.reverse middle.refs with
        | badRef | notThunk =>
          simp [thunk, typeError] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
        | isThunk mode value =>
          cases mode with
          | evaluated =>
            simp [thunk] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨targetArgs.1, ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, targetArgs.2]
            simp [opClass, thunk]
          | notEvaluated =>
            simp only [thunk] at run
            cases app : doOpApp [value, .conv none []] with
            | none =>
              simp [app, typeError] at run
              obtain ⟨_, rfl⟩ := run
              exact (safe rfl).elim
            | some pair =>
              obtain ⟨callEnv, body⟩ := pair
              simp only [app] at run
              by_cases zero : middle.clock = 0
              · simp [zero, timeoutError] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨targetArgs.1, ?_⟩
                rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, targetArgs.2]
                simp [opClass, thunk, app, zero, timeoutError]
              · simp only [zero, ↓reduceIte] at run
                cases callRun : evaluate (decClock middle) callEnv [body] with
                | mk after result =>
                  cases result with
                  | err error =>
                    simp only [callRun] at run
                    cases run
                    have targetCall := forceIH middle (.val values) values .notEvaluated value (callEnv, body) callEnv body
                      ⟨argsRun, rfl, opClass, thunk, rfl, app, rfl, zero⟩ s' (.err error)
                      ⟨callRun, by simpa [decClock] using targetArgs.1, safe⟩
                    refine ⟨targetCall.1, ?_⟩
                    rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, targetArgs.2]
                    simp only [opClass, thunk, app, zero, ↓reduceIte]
                    have targetCall' : evaluate (decClock { middle with evalState := es }) callEnv [body] =
                        ({ s' with evalState := es }, .err error) := by
                      simpa [decClock] using targetCall.2
                    rw [targetCall']
                  | val newValues =>
                    simp only [callRun] at run
                    cases updated : updateThunk values.reverse after.refs newValues with
                    | none =>
                      simp [updated, typeError] at run
                      obtain ⟨_, rfl⟩ := run
                      exact (safe rfl).elim
                    | some refs =>
                      simp only [updated] at run
                      cases run
                      have targetCall := forceIH middle (.val values) values .notEvaluated value (callEnv, body) callEnv body
                        ⟨argsRun, rfl, opClass, thunk, rfl, app, rfl, zero⟩ after (.val newValues)
                        ⟨callRun, by simpa [decClock] using targetArgs.1, by simp⟩
                      refine ⟨targetCall.1, ?_⟩
                      rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, targetArgs.2]
                      simp only [opClass, thunk, app, zero, ↓reduceIte]
                      have targetCall' : evaluate (decClock { middle with evalState := es }) callEnv [body] =
                          ({ after with evalState := es }, .val newValues) := by
                        simpa [decClock] using targetCall.2
                      rw [targetCall']
                      simp [updated]
      | evalOp =>
        rw [opClass, fixClockDoEvalRes] at run
        simp [doEvalRes, doEval, targetArgs.1] at run
        obtain ⟨_, rfl⟩ := run
        exact (safe rfl).elim
end Flapjack.EvaluateProps
