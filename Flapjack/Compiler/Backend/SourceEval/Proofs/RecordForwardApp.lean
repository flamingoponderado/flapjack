module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordForwardControl

@[expose] public section

/-! Application case of recording-state preservation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Flapjack infrastructure: resetting the generation preserves the recording
step; HOL uses reset_env_generation_orac_eqs inline. -/
theorem recordingStep_reset {Config F : Type} (ci : CompilerInstance Config)
    (before after : State F) (base : Option EvalState) (step : RecordingStep ci before after) :
    RecordingStep ci before { after with evalState := resetEnvGeneration base after.evalState } := by
  have eqs := resetEnvGeneration_oracleEqs ci base after.evalState before.evalState
    (oracleState before.evalState).oracle
  exact ⟨eqs.1.mpr step.1, eqs.2.1.mpr step.2.1, by simpa [eqs.2.2.2.2.2] using step.2.2⟩

/-- The full application induction case preserves recording state. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluateIsRecordForward_App {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (ih :
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (pair : SemEnv Value × AstHOL.Exp) (callEnv : SemEnv Value) (body : AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .funApp ∧ doOpApp values.reverse = some pair ∧ pair = (callEnv, body) ∧
        middle.clock ≠ 0 → ExpsRecordAt ci (decClock middle) callEnv [body]) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (decoded : State F) (decodedResult : Result (SemEnv Value × List Dec) Value)
          (pair : SemEnv Value × List Dec) (evalEnv : SemEnv Value) (decs : List Dec),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .evalOp ∧ doEvalRes values.reverse middle = (decoded, decodedResult) ∧
        decodedResult = .val pair ∧ pair = (evalEnv, decs) ∧ decoded.clock ≠ 0 →
        DecsRecordAt ci (decClock decoded) evalEnv decs) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (mode : ThunkMode) (thunk : Value) (pair : SemEnv Value × AstHOL.Exp)
          (callEnv : SemEnv Value) (body : AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .force ∧ destThunk values.reverse middle.refs = .isThunk mode thunk ∧
        mode = .notEvaluated ∧ doOpApp [thunk, .conv none []] = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → ExpsRecordAt ci (decClock middle) callEnv [body]) ∧
      ExpsRecordAt ci s env args.reverse) : ExpsRecordAt ci s env [.app op args] := by
  obtain ⟨callIH, evalIH, forceIH, argsIH⟩ := ih
  intro s' res ⟨run, recorded⟩
  rw [evaluate, (fixClockEvaluate s env args.reverse []).1] at run
  cases argsRun : evaluate s env args.reverse with
  | mk middle argResult =>
    have firstStep := argsIH middle argResult ⟨argsRun, recorded⟩
    cases argResult with
    | err error => simp only [argsRun] at run; cases run; exact firstStep
    | val values =>
      simp only [argsRun] at run
      cases opClass : getOpClass op with
      | simple =>
        rw [opClass] at run
        cases app : doApp (middle.refs, middle.ffi) op values.reverse with
        | none =>
          simp [app, typeError] at run
          obtain ⟨rfl, _⟩ := run
          exact firstStep
        | some output =>
          rcases output with ⟨⟨refs, ffi⟩, result⟩
          simp only [app] at run
          cases run
          exact recordingStep_trans ci s middle _
            ⟨firstStep, recordingStep_sameEval ci middle _ firstStep.1 rfl⟩
      | funApp =>
        rw [opClass] at run
        cases app : doOpApp values.reverse with
        | none =>
          simp [app, typeError] at run
          obtain ⟨rfl, _⟩ := run
          exact firstStep
        | some pair =>
          obtain ⟨callEnv, body⟩ := pair
          simp only [app] at run
          by_cases zero : middle.clock = 0
          · simp [zero, timeoutError] at run
            obtain ⟨rfl, _⟩ := run
            exact firstStep
          · simp [zero] at run
            have lastStep := callIH middle (.val values) values (callEnv, body) callEnv body
              ⟨argsRun, rfl, opClass, app, rfl, zero⟩ s' res ⟨run, by simpa [decClock] using firstStep.1⟩
            exact recordingStep_trans ci s middle s' ⟨firstStep, by simpa [decClock, RecordingStep] using lastStep⟩
      | force =>
        rw [opClass] at run
        cases thunk : destThunk values.reverse middle.refs with
        | badRef | notThunk =>
          simp [thunk, typeError] at run
          obtain ⟨rfl, _⟩ := run
          exact firstStep
        | isThunk mode value =>
          cases mode with
          | evaluated =>
            simp [thunk] at run
            obtain ⟨rfl, _⟩ := run
            exact firstStep
          | notEvaluated =>
            simp only [thunk] at run
            cases app : doOpApp [value, .conv none []] with
            | none =>
              simp [app, typeError] at run
              obtain ⟨rfl, _⟩ := run
              exact firstStep
            | some pair =>
              obtain ⟨callEnv, body⟩ := pair
              simp only [app] at run
              by_cases zero : middle.clock = 0
              · simp [zero, timeoutError] at run
                obtain ⟨rfl, _⟩ := run
                exact firstStep
              · simp only [zero, ↓reduceIte] at run
                cases callRun : evaluate (decClock middle) callEnv [body] with
                | mk after result =>
                  have lastStep := forceIH middle (.val values) values .notEvaluated value (callEnv, body) callEnv body
                    ⟨argsRun, rfl, opClass, thunk, rfl, app, rfl, zero⟩ after result
                    ⟨callRun, by simpa [decClock] using firstStep.1⟩
                  have composed : RecordingStep ci s after := recordingStep_trans ci s middle after
                    ⟨firstStep, by simpa [decClock, RecordingStep] using lastStep⟩
                  cases result with
                  | err error => simp only [callRun] at run; cases run; exact composed
                  | val newValues =>
                    simp only [callRun] at run
                    cases updated : updateThunk values.reverse after.refs newValues with
                    | none =>
                      simp [updated, typeError] at run
                      obtain ⟨rfl, _⟩ := run
                      exact composed
                    | some refs =>
                      simp only [updated] at run
                      cases run
                      exact recordingStep_trans ci s after _
                        ⟨composed, recordingStep_sameEval ci after _ composed.1 rfl⟩
      | evalOp =>
        rw [opClass, fixClockDoEvalRes] at run
        cases decoded : doEval values.reverse middle.evalState with
        | none =>
          simp [doEvalRes, decoded] at run
          obtain ⟨rfl, _⟩ := run
          exact firstStep
        | some data =>
          obtain ⟨evalEnv, decs, evalState⟩ := data
          simp only [doEvalRes, decoded] at run
          have decodedFacts := insert_doEval values.reverse middle.evalState evalEnv decs evalState ci
            (oracleState middle.evalState).oracle ⟨decoded, firstStep.1⟩
          have decodedStep : RecordingStep ci middle { middle with evalState := evalState } :=
            ⟨decodedFacts.1, decodedFacts.2.1, decodedFacts.2.2.2⟩
          have initialStep := recordingStep_trans ci s middle _ ⟨firstStep, decodedStep⟩
          by_cases zero : middle.clock = 0
          · simp [zero, timeoutError] at run
            obtain ⟨rfl, _⟩ := run
            simpa [RecordingStep, zero] using initialStep
          · simp only [zero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2] at run
            have decIH := evalIH middle (.val values) values { middle with evalState := evalState }
              (.val (evalEnv, decs)) (evalEnv, decs) evalEnv decs
              ⟨argsRun, rfl, opClass, by simp [doEvalRes, decoded], rfl, rfl, zero⟩
            cases decRun : evaluateDecs (decClock { middle with evalState := evalState }) evalEnv decs with
            | mk after result =>
              have decStep := decIH after result ⟨decRun, by simpa [decClock] using decodedStep.1⟩
              have composed : RecordingStep ci s after := recordingStep_trans ci s _ after
                ⟨initialStep, by simpa [decClock, RecordingStep] using decStep⟩
              cases result with
              | err error =>
                cases error with
                | abort error => simp only [decRun] at run; cases run; exact composed
                | raise value =>
                  simp only [decRun] at run
                  cases run
                  exact recordingStep_reset ci s after middle.evalState composed
              | val newEnv =>
                simp only [decRun] at run
                cases declared : declareEnv after.evalState (extendDecEnv newEnv evalEnv) with
                | none =>
                  simp [declared, typeError] at run
                  obtain ⟨rfl, _⟩ := run
                  exact composed
                | some declaration =>
                  obtain ⟨value, finalState⟩ := declaration
                  simp only [declared] at run
                  cases run
                  have facts := insert_declareEnv after.evalState (extendDecEnv newEnv evalEnv) value finalState ci
                    (oracleState after.evalState).oracle ⟨declared, composed.1⟩
                  have finalStep : RecordingStep ci after { after with evalState := finalState } :=
                    ⟨facts.1, facts.2.1, facts.2.2.2⟩
                  have complete := recordingStep_trans ci s after _ ⟨composed, finalStep⟩
                  exact recordingStep_reset ci s { after with evalState := finalState } middle.evalState complete
end Flapjack.Compiler.Backend.SourceEval.Proofs
