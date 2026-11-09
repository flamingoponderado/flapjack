module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.InsertCorrectControl

@[expose] public section
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insertOracleCorrect_App {Config F : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun)
    (s : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (ih :
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (pair : SemEnv Value × AstHOL.Exp) (callEnv : SemEnv Value) (body : AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .funApp ∧ doOpApp values.reverse = some pair ∧ pair = (callEnv, body) ∧
        middle.clock ≠ 0 → ExpsInsertAt ci oracle (decClock middle) callEnv [body]) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (decoded : State F) (decodedResult : Result (SemEnv Value × List Dec) Value)
          (pair : SemEnv Value × List Dec) (evalEnv : SemEnv Value) (decs : List Dec),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .evalOp ∧ doEvalRes values.reverse middle = (decoded, decodedResult) ∧
        decodedResult = .val pair ∧ pair = (evalEnv, decs) ∧ decoded.clock ≠ 0 →
        DecsInsertAt ci oracle (decClock decoded) evalEnv decs) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (mode : ThunkMode) (thunk : Value) (pair : SemEnv Value × AstHOL.Exp)
          (callEnv : SemEnv Value) (body : AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .force ∧ destThunk values.reverse middle.refs = .isThunk mode thunk ∧
        mode = .notEvaluated ∧ doOpApp [thunk, .conv none []] = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → ExpsInsertAt ci oracle (decClock middle) callEnv [body]) ∧
      ExpsInsertAt ci oracle s env args.reverse) : ExpsInsertAt ci oracle s env [.app op args] := by
  obtain ⟨callIH, evalIH, forceIH, argsIH⟩ := ih
  intro s' res ⟨run, recorded, agrees, wf, safe⟩
  rw [evaluate, (fixClockEvaluate s env args.reverse []).1] at run
  cases argsRun : evaluate s env args.reverse with
  | mk middle argResult =>
    cases argResult with
    | err error =>
      simp only [argsRun] at run
      cases run
      have target := argsIH s' (.err error) ⟨argsRun, recorded, agrees, wf, safe⟩
      rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, target]
    | val values =>
      simp only [argsRun] at run
      have firstRecorded := (evaluate_is_record_forward ci).1 s env args.reverse middle (.val values)
        ⟨argsRun, recorded⟩
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
          have target := argsIH middle (.val values) ⟨argsRun, recorded, agrees, wf, by simp⟩
          rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, target]
          simp [opClass, insertOracleState, app]
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
            have target := argsIH middle (.val values) ⟨argsRun, recorded, agrees, wf, by simp⟩
            rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, target]
            simp [opClass, app, insertOracleState, zero, timeoutError]
          · simp only [zero, ↓reduceIte] at run
            have lastRecorded := (evaluate_is_record_forward ci).1 (decClock middle) callEnv [body] s' res
              ⟨run, by simpa [decClock] using firstRecorded.1⟩
            have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState
              ⟨agrees, by simpa [decClock] using lastRecorded.2.1⟩
            have targetArgs := argsIH middle (.val values) ⟨argsRun, recorded, agreesMiddle, wf, by simp⟩
            have targetCall := callIH middle (.val values) values (callEnv, body) callEnv body
              ⟨argsRun, rfl, opClass, app, rfl, zero⟩ s' res
              ⟨run, by simpa [decClock] using firstRecorded.1, agrees, wf, safe⟩
            rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, targetArgs]
            simpa [opClass, app, insertOracleState, decClock, zero] using targetCall
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
            have target := argsIH middle (.val values) ⟨argsRun, recorded, agrees, wf, by simp⟩
            rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, target]
            simp [opClass, insertOracleState, thunk]
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
                have target := argsIH middle (.val values) ⟨argsRun, recorded, agrees, wf, by simp⟩
                rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, target]
                simp [opClass, insertOracleState, thunk, app, zero, timeoutError]
              · simp only [zero, ↓reduceIte] at run
                cases callRun : evaluate (decClock middle) callEnv [body] with
                | mk after result =>
                  have lastRecorded := (evaluate_is_record_forward ci).1 (decClock middle) callEnv [body] after result
                    ⟨callRun, by simpa [decClock] using firstRecorded.1⟩
                  cases result with
                  | err error =>
                    simp only [callRun] at run
                    cases run
                    have agreesMiddle := oracleAgrees_backward oracle s'.evalState middle.evalState
                      ⟨agrees, by simpa [decClock] using lastRecorded.2.1⟩
                    have targetArgs := argsIH middle (.val values) ⟨argsRun, recorded, agreesMiddle, wf, by simp⟩
                    have targetCall := forceIH middle (.val values) values .notEvaluated value (callEnv, body) callEnv body
                      ⟨argsRun, rfl, opClass, thunk, rfl, app, rfl, zero⟩ s' (.err error)
                      ⟨callRun, by simpa [decClock] using firstRecorded.1, agrees, wf, safe⟩
                    have targetCall' : evaluate (decClock (insertOracleState ci oracle middle)) callEnv [body] =
                        (insertOracleState ci oracle s', .err error) := by
                      simpa [insertOracleState, decClock] using targetCall
                    rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, targetArgs]
                    simp only [opClass]
                    simp only [insertOracleState, thunk, app, zero, ↓reduceIte] at targetCall' ⊢
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
                      have agreesMiddle := oracleAgrees_backward oracle after.evalState middle.evalState
                        ⟨agrees, by simpa [decClock] using lastRecorded.2.1⟩
                      have targetArgs := argsIH middle (.val values) ⟨argsRun, recorded, agreesMiddle, wf, by simp⟩
                      have targetCall := forceIH middle (.val values) values .notEvaluated value (callEnv, body) callEnv body
                        ⟨argsRun, rfl, opClass, thunk, rfl, app, rfl, zero⟩ after (.val newValues)
                        ⟨callRun, by simpa [decClock] using firstRecorded.1, agrees, wf, by simp⟩
                      have targetCall' : evaluate (decClock (insertOracleState ci oracle middle)) callEnv [body] =
                          (insertOracleState ci oracle after, .val newValues) := by
                        simpa [insertOracleState, decClock] using targetCall
                      rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, targetArgs]
                      simp only [opClass, insertOracleState, thunk, app, zero, ↓reduceIte] at targetCall' ⊢
                      rw [targetCall']
                      simp [updated]
      | evalOp =>
        rw [opClass, fixClockDoEvalRes] at run
        cases decoded : doEval values.reverse middle.evalState with
        | none =>
          simp [doEvalRes, decoded] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
        | some data =>
          obtain ⟨evalEnv, decs, evalState⟩ := data
          simp only [doEvalRes, decoded] at run
          have facts := insert_doEval values.reverse middle.evalState evalEnv decs evalState ci oracle
            ⟨decoded, firstRecorded.1⟩
          by_cases zero : middle.clock = 0
          · simp [zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            have agreesMiddle := oracleAgrees_backward oracle evalState middle.evalState ⟨agrees, facts.2.1⟩
            have targetArgs := argsIH middle (.val values) ⟨argsRun, recorded, agreesMiddle, wf, by simp⟩
            have targetDecoded := facts.2.2.1 ⟨agrees, wf⟩
            rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, targetArgs]
            dsimp only
            rw [opClass, fixClockDoEvalRes]
            simp [doEvalRes, insertOracleState, targetDecoded, zero, timeoutError]
          · simp only [zero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2] at run
            have decIH := evalIH middle (.val values) values { middle with evalState := evalState }
              (.val (evalEnv, decs)) (evalEnv, decs) evalEnv decs
              ⟨argsRun, rfl, opClass, by simp [doEvalRes, decoded], rfl, rfl, zero⟩
            cases decRun : evaluateDecs (decClock { middle with evalState := evalState }) evalEnv decs with
            | mk after result =>
              have lastRecorded := (evaluate_is_record_forward ci).2.2
                (decClock { middle with evalState := evalState }) evalEnv decs after result
                ⟨decRun, by simpa [decClock] using facts.1⟩
              cases result with
              | err error =>
                cases error with
                | abort error =>
                  simp only [decRun] at run
                  cases run
                  have agreesDecoded := oracleAgrees_backward oracle s'.evalState evalState
                    ⟨agrees, by simpa [decClock] using lastRecorded.2.1⟩
                  have agreesMiddle := oracleAgrees_backward oracle evalState middle.evalState ⟨agreesDecoded, facts.2.1⟩
                  have targetArgs := argsIH middle (.val values) ⟨argsRun, recorded, agreesMiddle, wf, by simp⟩
                  have targetDecoded := facts.2.2.1 ⟨agreesDecoded, wf⟩
                  have targetDec := decIH s' (.err (.abort error))
                    ⟨decRun, by simpa [decClock] using facts.1, agrees, wf, by intro h; apply safe; cases h; rfl⟩
                  have targetDec' : evaluateDecs (decClock { insertOracleState ci oracle middle with
                      evalState := insertGenOracle ci id (fun args => args.1.1) oracle evalState }) evalEnv decs =
                      (insertOracleState ci oracle s', .err (.abort error)) := by
                    simpa [insertOracleState, decClock] using targetDec
                  rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, targetArgs]
                  dsimp only
                  rw [opClass, fixClockDoEvalRes]
                  simp only [doEvalRes, insertOracleState, targetDecoded, zero, ↓reduceIte] at targetDec' ⊢
                  rw [(fixClockEvaluate _ _ [] _).2, targetDec']
                | raise value =>
                  simp only [decRun] at run
                  cases run
                  have resetFacts := resetEnvGeneration_oracleEqs ci middle.evalState after.evalState middle.evalState oracle
                  have agreesAfter := resetFacts.2.2.1.mp agrees
                  have agreesDecoded := oracleAgrees_backward oracle after.evalState evalState
                    ⟨agreesAfter, by simpa [decClock] using lastRecorded.2.1⟩
                  have agreesMiddle := oracleAgrees_backward oracle evalState middle.evalState ⟨agreesDecoded, facts.2.1⟩
                  have targetArgs := argsIH middle (.val values) ⟨argsRun, recorded, agreesMiddle, wf, by simp⟩
                  have targetDecoded := facts.2.2.1 ⟨agreesDecoded, wf⟩
                  have targetDec := decIH after (.err (.raise value))
                    ⟨decRun, by simpa [decClock] using facts.1, agreesAfter, wf, by simp⟩
                  have targetDec' : evaluateDecs (decClock { insertOracleState ci oracle middle with
                      evalState := insertGenOracle ci id (fun args => args.1.1) oracle evalState }) evalEnv decs =
                      (insertOracleState ci oracle after, .err (.raise value)) := by
                    simpa [insertOracleState, decClock] using targetDec
                  rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, targetArgs]
                  dsimp only
                  rw [opClass, fixClockDoEvalRes]
                  simp only [doEvalRes, insertOracleState, targetDecoded, zero, ↓reduceIte] at targetDec' ⊢
                  rw [(fixClockEvaluate _ _ [] _).2, targetDec']
                  dsimp only
                  rw [(resetEnvGeneration_oracleEqs ci (insertGenOracle ci id (fun args => args.1.1) oracle after.evalState)
                    after.evalState middle.evalState oracle).2.2.2.1]
                  rw [(resetEnvGeneration_oracleEqs ci after.evalState after.evalState middle.evalState oracle).2.2.2.2.1]
              | val newEnv =>
                simp only [decRun] at run
                cases declared : declareEnv after.evalState (extendDecEnv newEnv evalEnv) with
                | none =>
                  simp [declared, typeError] at run
                  obtain ⟨_, rfl⟩ := run
                  exact (safe rfl).elim
                | some declaration =>
                  obtain ⟨value, finalState⟩ := declaration
                  simp only [declared] at run
                  cases run
                  have agreesFinal := (resetEnvGeneration_oracleEqs ci middle.evalState finalState middle.evalState oracle).2.2.1.mp agrees
                  have declFacts := insert_declareEnv after.evalState (extendDecEnv newEnv evalEnv) value finalState ci oracle
                    ⟨declared, lastRecorded.1⟩
                  have agreesAfter := oracleAgrees_backward oracle finalState after.evalState ⟨agreesFinal, declFacts.2.1⟩
                  have agreesDecoded := oracleAgrees_backward oracle after.evalState evalState
                    ⟨agreesAfter, by simpa [decClock] using lastRecorded.2.1⟩
                  have agreesMiddle := oracleAgrees_backward oracle evalState middle.evalState ⟨agreesDecoded, facts.2.1⟩
                  have targetArgs := argsIH middle (.val values) ⟨argsRun, recorded, agreesMiddle, wf, by simp⟩
                  have targetDecoded := facts.2.2.1 ⟨agreesDecoded, wf⟩
                  have targetDeclared := declFacts.2.2.1 agreesFinal
                  have targetDec := decIH after (.val newEnv)
                    ⟨decRun, by simpa [decClock] using facts.1, agreesAfter, wf, by simp⟩
                  have targetDec' : evaluateDecs (decClock { insertOracleState ci oracle middle with
                      evalState := insertGenOracle ci id (fun args => args.1.1) oracle evalState }) evalEnv decs =
                      (insertOracleState ci oracle after, .val newEnv) := by
                    simpa [insertOracleState, decClock] using targetDec
                  rw [evaluate, (fixClockEvaluate (insertOracleState ci oracle s) env args.reverse []).1, targetArgs]
                  dsimp only
                  rw [opClass, fixClockDoEvalRes]
                  simp only [doEvalRes, insertOracleState, targetDecoded, zero, ↓reduceIte] at targetDec' ⊢
                  rw [(fixClockEvaluate _ _ [] _).2, targetDec']
                  dsimp only
                  rw [targetDeclared]
                  dsimp only
                  rw [(resetEnvGeneration_oracleEqs ci (insertGenOracle ci id (fun args => args.1.1) oracle finalState)
                    finalState middle.evalState oracle).2.2.2.1]
                  rw [(resetEnvGeneration_oracleEqs ci finalState finalState middle.evalState oracle).2.2.2.2.1]
end Flapjack.Compiler.Backend.SourceEval.Proofs
