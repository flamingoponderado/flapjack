import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordSuffixLog
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
/-- The full application case of recording-oracle clock suffix. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_record_suffix"]
theorem evaluateRecordSuffix_App {Config F : Type} (ci : CompilerInstance Config) (k : Nat)
    (s : State F) (env : SemEnv Value) (op : Op) (args : List AstHOL.Exp)
    (ih :
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (pair : SemEnv Value × AstHOL.Exp) (callEnv : SemEnv Value) (body : AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .funApp ∧ doOpApp values.reverse = some pair ∧ pair = (callEnv, body) ∧
        middle.clock ≠ 0 → ExpsSuffixAt ci k (decClock middle) callEnv [body]) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (decoded : State F) (decodedResult : Result (SemEnv Value × List Dec) Value)
          (pair : SemEnv Value × List Dec) (evalEnv : SemEnv Value) (decs : List Dec),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .evalOp ∧ doEvalRes values.reverse middle = (decoded, decodedResult) ∧
        decodedResult = .val pair ∧ pair = (evalEnv, decs) ∧ decoded.clock ≠ 0 →
        DecsSuffixAt ci k (decClock decoded) evalEnv decs) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (mode : ThunkMode) (thunk : Value) (pair : SemEnv Value × AstHOL.Exp)
          (callEnv : SemEnv Value) (body : AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .force ∧ destThunk values.reverse middle.refs = .isThunk mode thunk ∧
        mode = .notEvaluated ∧ doOpApp [thunk, .conv none []] = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → ExpsSuffixAt ci k (decClock middle) callEnv [body]) ∧
      ExpsSuffixAt ci k s env args.reverse) : ExpsSuffixAt ci k s env [.app op args] := by
  obtain ⟨callIH, evalIH, forceIH, argsIH⟩ := ih
  intro s' res ⟨run, recorded, bound⟩
  rw [evaluate, (fixClockEvaluate s env args.reverse []).1] at run
  cases argsRun : evaluate s env args.reverse with
  | mk middle argResult =>
    have firstSuffix := argsIH middle argResult ⟨argsRun, recorded, bound⟩
    have firstRecorded := (evaluate_is_record_forward ci).1 s env args.reverse middle argResult ⟨argsRun, recorded⟩
    cases argResult with
    | err error =>
      simp only [argsRun] at run
      cases run
      rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
      · left
        refine ⟨bound', ?_⟩
        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
      · right
        refine ⟨short, ?_, forward⟩
        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
    | val values =>
      simp only [argsRun] at run
      cases opClass : getOpClass op with
      | simple =>
        rw [opClass] at run
        cases app : doApp (middle.refs, middle.ffi) op values.reverse with
        | none =>
          simp [app, typeError] at run
          obtain ⟨rfl, rfl⟩ := run
          rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
            simp [opClass, app, typeError]
          · right
            refine ⟨short, ?_, forward⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
        | some output =>
          obtain ⟨⟨refs, ffi⟩, result⟩ := output
          simp only [app] at run
          cases run
          rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
            simp [opClass, app]
          · right
            refine ⟨short, ?_, forward⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
      | funApp =>
        rw [opClass] at run
        cases app : doOpApp values.reverse with
        | none =>
          simp [app, typeError] at run
          obtain ⟨rfl, rfl⟩ := run
          rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
            simp [opClass, app, typeError]
          · right
            refine ⟨short, ?_, forward⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
        | some pair =>
          obtain ⟨callEnv, body⟩ := pair
          simp only [app] at run
          by_cases zero : middle.clock = 0
          · simp [zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
            · left
              refine ⟨bound', ?_⟩
              rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
              simp [opClass, app, zero, timeoutError]
            · right
              refine ⟨short, ?_, forward⟩
              rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
          · simp only [zero, ↓reduceIte] at run
            have lastRecorded := (evaluate_is_record_forward ci).1 (decClock middle) callEnv [body] s' res
              ⟨run, by simpa [decClock] using firstRecorded.1⟩
            have forward : recordForward middle.evalState s'.evalState := by simpa [decClock] using lastRecorded.2.1
            rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
            · by_cases enough : k ≤ (decClock middle).clock
              · have suffix := callIH middle (.val values) values (callEnv, body) callEnv body
                  ⟨argsRun, rfl, opClass, app, rfl, zero⟩ s' res
                  ⟨run, by simpa [decClock] using firstRecorded.1, enough⟩
                have nonzero : middle.clock - k ≠ 0 := by simp only [decClock] at enough; omega
                rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, laterForward⟩
                · left
                  refine ⟨bound', ?_⟩
                  rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                  simp only [opClass, app]
                  simp only [decClock] at equal
                  simpa [decClock, nonzero, Nat.sub_sub, Nat.add_comm] using equal
                · right
                  refine ⟨short, ?_, laterForward⟩
                  rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                  simp only [opClass, app]
                  simp only [decClock] at equal
                  simpa [decClock, nonzero, Nat.sub_sub, Nat.add_comm] using equal
              · have exhausted : middle.clock - k = 0 := by simp only [decClock] at enough; omega
                right
                refine ⟨{ middle with clock := middle.clock - k }, ?_, by simpa using forward⟩
                rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                simp [opClass, app, exhausted, timeoutError]
            · right
              refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, forward⟩⟩
              rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
      | force =>
        rw [opClass] at run
        cases thunk : destThunk values.reverse middle.refs with
        | badRef | notThunk =>
          simp [thunk, typeError] at run
          obtain ⟨rfl, rfl⟩ := run
          rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
            simp [opClass, thunk, typeError]
          · right
            refine ⟨short, ?_, forward⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
        | isThunk mode value =>
          cases mode with
          | evaluated =>
            simp [thunk] at run
            obtain ⟨rfl, rfl⟩ := run
            rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
            · left
              refine ⟨bound', ?_⟩
              rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
              simp [opClass, thunk]
            · right
              refine ⟨short, ?_, forward⟩
              rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
          | notEvaluated =>
            simp only [thunk] at run
            cases app : doOpApp [value, .conv none []] with
            | none =>
              simp [app, typeError] at run
              obtain ⟨rfl, rfl⟩ := run
              rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
              · left
                refine ⟨bound', ?_⟩
                rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
                simp [opClass, thunk, app, typeError]
              · right
                refine ⟨short, ?_, forward⟩
                rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
            | some pair =>
              obtain ⟨callEnv, body⟩ := pair
              simp only [app] at run
              by_cases zero : middle.clock = 0
              · simp [zero, timeoutError] at run
                obtain ⟨rfl, rfl⟩ := run
                rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
                · left
                  refine ⟨bound', ?_⟩
                  rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
                  simp [opClass, thunk, app, zero, timeoutError]
                · right
                  refine ⟨short, ?_, forward⟩
                  rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
              · simp only [zero, ↓reduceIte] at run
                cases callRun : evaluate (decClock middle) callEnv [body] with
                | mk after result =>
                  have lastRecorded := (evaluate_is_record_forward ci).1 (decClock middle) callEnv [body] after result
                    ⟨callRun, by simpa [decClock] using firstRecorded.1⟩
                  cases result with
                  | err error =>
                    simp only [callRun] at run
                    cases run
                    have forward : recordForward middle.evalState s'.evalState := by simpa [decClock] using lastRecorded.2.1
                    rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
                    · by_cases enough : k ≤ (decClock middle).clock
                      · have suffix := forceIH middle (.val values) values .notEvaluated value (callEnv, body) callEnv body
                          ⟨argsRun, rfl, opClass, thunk, rfl, app, rfl, zero⟩ s' (.err error)
                          ⟨callRun, by simpa [decClock] using firstRecorded.1, enough⟩
                        have nonzero : middle.clock - k ≠ 0 := by simp only [decClock] at enough; omega
                        rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, laterForward⟩
                        · left
                          refine ⟨bound', ?_⟩
                          rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                          simp only [opClass, thunk, app, nonzero, ↓reduceIte]
                          simp only [decClock] at equal
                          have equal' : evaluate (decClock { middle with clock := middle.clock - k }) callEnv [body] =
                              ({ s' with clock := s'.clock - k }, .err error) := by
                            simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                          rw [equal']
                        · right
                          refine ⟨short, ?_, laterForward⟩
                          rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                          simp only [opClass, thunk, app, nonzero, ↓reduceIte]
                          simp only [decClock] at equal
                          have equal' : evaluate (decClock { middle with clock := middle.clock - k }) callEnv [body] =
                              (short, .err (.abort .timeoutError)) := by
                            simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                          rw [equal']
                      · have exhausted : middle.clock - k = 0 := by simp only [decClock] at enough; omega
                        right
                        refine ⟨{ middle with clock := middle.clock - k }, ?_, by simpa using forward⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                        simp [opClass, thunk, app, exhausted, timeoutError]
                    · right
                      refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, forward⟩⟩
                      rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                  | val newValues =>
                    simp only [callRun] at run
                    cases updated : updateThunk values.reverse after.refs newValues <;>
                      simp [updated, typeError] at run <;> obtain ⟨rfl, rfl⟩ := run
                    all_goals
                      have forward : recordForward middle.evalState after.evalState := by simpa [decClock] using lastRecorded.2.1
                      rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
                      · by_cases enough : k ≤ (decClock middle).clock
                        · have suffix := forceIH middle (.val values) values .notEvaluated value (callEnv, body) callEnv body
                            ⟨argsRun, rfl, opClass, thunk, rfl, app, rfl, zero⟩ after (.val newValues)
                            ⟨callRun, by simpa [decClock] using firstRecorded.1, enough⟩
                          have nonzero : middle.clock - k ≠ 0 := by simp only [decClock] at enough; omega
                          rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, laterForward⟩
                          · left
                            refine ⟨bound', ?_⟩
                            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                            simp only [opClass, thunk, app, nonzero, ↓reduceIte]
                            have equal' : evaluate (decClock { middle with clock := middle.clock - k }) callEnv [body] =
                                ({ after with clock := after.clock - k }, .val newValues) := by
                              simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                            rw [equal']
                            simp [updated, typeError]
                          · right
                            refine ⟨short, ?_, laterForward⟩
                            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                            simp only [opClass, thunk, app, nonzero, ↓reduceIte]
                            have equal' : evaluate (decClock { middle with clock := middle.clock - k }) callEnv [body] =
                                (short, .err (.abort .timeoutError)) := by
                              simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                            rw [equal']
                        · have exhausted : middle.clock - k = 0 := by simp only [decClock] at enough; omega
                          right
                          refine ⟨{ middle with clock := middle.clock - k }, ?_, by simpa using forward⟩
                          rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                          simp [opClass, thunk, app, exhausted, timeoutError]
                      · right
                        refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, forward⟩⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
      | evalOp =>
        rw [opClass, fixClockDoEvalRes] at run
        cases decoded : doEval values.reverse middle.evalState with
        | none =>
          simp [doEvalRes, decoded] at run
          obtain ⟨rfl, rfl⟩ := run
          rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
          · left
            refine ⟨bound', ?_⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
            dsimp only
            rw [opClass, fixClockDoEvalRes]
            simp [doEvalRes, decoded]
          · right
            refine ⟨short, ?_, forward⟩
            rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
        | some data =>
          obtain ⟨evalEnv, decs, evalState⟩ := data
          simp only [doEvalRes, decoded] at run
          have decodedFacts := insert_doEval values.reverse middle.evalState evalEnv decs evalState ci
            (oracleState middle.evalState).oracle ⟨decoded, firstRecorded.1⟩
          by_cases zero : middle.clock = 0
          · simp [zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            rcases firstSuffix with ⟨bound', equal⟩ | ⟨short, equal, forward⟩
            · left
              refine ⟨by simpa [zero] using bound', ?_⟩
              rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
              dsimp only
              rw [opClass, fixClockDoEvalRes]
              simp [doEvalRes, decoded, zero, timeoutError]
            · right
              refine ⟨short, ?_, recordForward_trans _ _ _ ⟨forward, decodedFacts.2.1⟩⟩
              rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, equal]
          · simp only [zero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2] at run
            have decIH := evalIH middle (.val values) values { middle with evalState := evalState }
              (.val (evalEnv, decs)) (evalEnv, decs) evalEnv decs
              ⟨argsRun, rfl, opClass, by simp [doEvalRes, decoded], rfl, rfl, zero⟩
            cases decRun : evaluateDecs (decClock { middle with evalState := evalState }) evalEnv decs with
            | mk after result =>
              have lastRecorded := (evaluate_is_record_forward ci).2.2
                (decClock { middle with evalState := evalState }) evalEnv decs after result
                ⟨decRun, by simpa [decClock] using decodedFacts.1⟩
              cases result with
              | err error =>
                cases error with
                | abort error =>
                  simp only [decRun] at run
                  cases run
                  have forwardDecoded : recordForward evalState s'.evalState := by simpa [decClock] using lastRecorded.2.1
                  have forwardMiddle := recordForward_trans _ _ _ ⟨decodedFacts.2.1, forwardDecoded⟩
                  rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
                  · by_cases enough : k ≤ (decClock { middle with evalState := evalState }).clock
                    · have suffix := decIH s' (.err (.abort error))
                        ⟨decRun, by simpa [decClock] using decodedFacts.1, enough⟩
                      have nonzero : middle.clock - k ≠ 0 := by simp only [decClock] at enough; omega
                      rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, laterForward⟩
                      · left
                        refine ⟨bound', ?_⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                        dsimp only
                        rw [opClass, fixClockDoEvalRes]
                        simp only [doEvalRes, decoded, nonzero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2]
                        have equal' : evaluateDecs (decClock { middle with clock := middle.clock - k, evalState := evalState }) evalEnv decs =
                            ({ s' with clock := s'.clock - k }, .err (.abort error)) := by
                          simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                        rw [equal']
                      · right
                        refine ⟨short, ?_, laterForward⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                        dsimp only
                        rw [opClass, fixClockDoEvalRes]
                        simp only [doEvalRes, decoded, nonzero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2]
                        have equal' : evaluateDecs (decClock { middle with clock := middle.clock - k, evalState := evalState }) evalEnv decs =
                            (short, .err (.abort .timeoutError)) := by
                          simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                        rw [equal']
                    · have exhausted : middle.clock - k = 0 := by simp only [decClock] at enough; omega
                      right
                      refine ⟨{ middle with clock := middle.clock - k, evalState := evalState }, ?_, by simpa using forwardDecoded⟩
                      rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                      dsimp only
                      rw [opClass, fixClockDoEvalRes]
                      simp [doEvalRes, decoded, exhausted, timeoutError]
                  · right
                    refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, forwardMiddle⟩⟩
                    rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                | raise value =>
                  simp only [decRun] at run
                  cases run
                  have forwardDecoded : recordForward evalState after.evalState := by simpa [decClock] using lastRecorded.2.1
                  have forwardMiddle := recordForward_trans _ _ _ ⟨decodedFacts.2.1, forwardDecoded⟩
                  have resetForward (es : Option EvalState) (h : recordForward es after.evalState) :
                      recordForward es (resetEnvGeneration middle.evalState after.evalState) :=
                    (resetEnvGeneration_oracleEqs ci middle.evalState after.evalState es (oracleState es).oracle).2.1.mpr h
                  rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
                  · by_cases enough : k ≤ (decClock { middle with evalState := evalState }).clock
                    · have suffix := decIH after (.err (.raise value))
                        ⟨decRun, by simpa [decClock] using decodedFacts.1, enough⟩
                      have nonzero : middle.clock - k ≠ 0 := by simp only [decClock] at enough; omega
                      rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, laterForward⟩
                      · left
                        refine ⟨bound', ?_⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                        dsimp only
                        rw [opClass, fixClockDoEvalRes]
                        simp only [doEvalRes, decoded, nonzero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2]
                        have equal' : evaluateDecs (decClock { middle with clock := middle.clock - k, evalState := evalState }) evalEnv decs =
                            ({ after with clock := after.clock - k }, .err (.raise value)) := by
                          simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                        rw [equal']
                      · right
                        refine ⟨short, ?_, resetForward _ laterForward⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                        dsimp only
                        rw [opClass, fixClockDoEvalRes]
                        simp only [doEvalRes, decoded, nonzero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2]
                        have equal' : evaluateDecs (decClock { middle with clock := middle.clock - k, evalState := evalState }) evalEnv decs =
                            (short, .err (.abort .timeoutError)) := by
                          simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                        rw [equal']
                    · have exhausted : middle.clock - k = 0 := by simp only [decClock] at enough; omega
                      right
                      refine ⟨{ middle with clock := middle.clock - k, evalState := evalState }, ?_, resetForward _ forwardDecoded⟩
                      rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                      dsimp only
                      rw [opClass, fixClockDoEvalRes]
                      simp [doEvalRes, decoded, exhausted, timeoutError]
                  · right
                    refine ⟨short, ?_, resetForward _ (recordForward_trans _ _ _ ⟨firstForward, forwardMiddle⟩)⟩
                    rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
              | val newEnv =>
                simp only [decRun] at run
                cases declared : declareEnv after.evalState (extendDecEnv newEnv evalEnv) with
                | none =>
                  simp [declared, typeError] at run
                  obtain ⟨rfl, rfl⟩ := run
                  have forwardDecoded : recordForward evalState after.evalState := by simpa [decClock] using lastRecorded.2.1
                  have forwardMiddle := recordForward_trans _ _ _ ⟨decodedFacts.2.1, forwardDecoded⟩
                  rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
                  · by_cases enough : k ≤ (decClock { middle with evalState := evalState }).clock
                    · have suffix := decIH after (.val newEnv)
                        ⟨decRun, by simpa [decClock] using decodedFacts.1, enough⟩
                      have nonzero : middle.clock - k ≠ 0 := by simp only [decClock] at enough; omega
                      rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, laterForward⟩
                      · left
                        refine ⟨bound', ?_⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                        dsimp only
                        rw [opClass, fixClockDoEvalRes]
                        simp only [doEvalRes, decoded, nonzero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2]
                        have equal' : evaluateDecs (decClock { middle with clock := middle.clock - k, evalState := evalState }) evalEnv decs =
                            ({ after with clock := after.clock - k }, .val newEnv) := by
                          simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                        rw [equal']
                        simp [declared, typeError]
                      · right
                        refine ⟨short, ?_, laterForward⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                        dsimp only
                        rw [opClass, fixClockDoEvalRes]
                        simp only [doEvalRes, decoded, nonzero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2]
                        have equal' : evaluateDecs (decClock { middle with clock := middle.clock - k, evalState := evalState }) evalEnv decs =
                            (short, .err (.abort .timeoutError)) := by
                          simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                        rw [equal']
                    · have exhausted : middle.clock - k = 0 := by simp only [decClock] at enough; omega
                      right
                      refine ⟨{ middle with clock := middle.clock - k, evalState := evalState }, ?_, by simpa using forwardDecoded⟩
                      rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                      dsimp only
                      rw [opClass, fixClockDoEvalRes]
                      simp [doEvalRes, decoded, exhausted, timeoutError]
                  · right
                    refine ⟨short, ?_, recordForward_trans _ _ _ ⟨firstForward, forwardMiddle⟩⟩
                    rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                | some declaration =>
                  obtain ⟨value, finalState⟩ := declaration
                  simp only [declared] at run
                  cases run
                  have declFacts := insert_declareEnv after.evalState (extendDecEnv newEnv evalEnv) value finalState ci
                    (oracleState after.evalState).oracle ⟨declared, lastRecorded.1⟩
                  have forwardDecoded : recordForward evalState after.evalState := by simpa [decClock] using lastRecorded.2.1
                  have forwardMiddle := recordForward_trans _ _ _ ⟨decodedFacts.2.1, forwardDecoded⟩
                  have finalForward (es : Option EvalState) (h : recordForward es after.evalState) :
                      recordForward es (resetEnvGeneration middle.evalState finalState) := by
                    have forward := recordForward_trans _ _ _ ⟨h, declFacts.2.1⟩
                    exact (resetEnvGeneration_oracleEqs ci middle.evalState finalState es (oracleState es).oracle).2.1.mpr forward
                  rcases firstSuffix with ⟨midBound, firstEqual⟩ | ⟨short, firstEqual, firstForward⟩
                  · by_cases enough : k ≤ (decClock { middle with evalState := evalState }).clock
                    · have suffix := decIH after (.val newEnv)
                        ⟨decRun, by simpa [decClock] using decodedFacts.1, enough⟩
                      have nonzero : middle.clock - k ≠ 0 := by simp only [decClock] at enough; omega
                      rcases suffix with ⟨bound', equal⟩ | ⟨short, equal, laterForward⟩
                      · left
                        refine ⟨bound', ?_⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                        dsimp only
                        rw [opClass, fixClockDoEvalRes]
                        simp only [doEvalRes, decoded, nonzero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2]
                        have equal' : evaluateDecs (decClock { middle with clock := middle.clock - k, evalState := evalState }) evalEnv decs =
                            ({ after with clock := after.clock - k }, .val newEnv) := by
                          simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                        rw [equal']
                        simp [declared]
                      · right
                        refine ⟨short, ?_, finalForward _ laterForward⟩
                        rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                        dsimp only
                        rw [opClass, fixClockDoEvalRes]
                        simp only [doEvalRes, decoded, nonzero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2]
                        have equal' : evaluateDecs (decClock { middle with clock := middle.clock - k, evalState := evalState }) evalEnv decs =
                            (short, .err (.abort .timeoutError)) := by
                          simpa [decClock, Nat.sub_sub, Nat.add_comm] using equal
                        rw [equal']
                    · have exhausted : middle.clock - k = 0 := by simp only [decClock] at enough; omega
                      right
                      refine ⟨{ middle with clock := middle.clock - k, evalState := evalState }, ?_, finalForward _ forwardDecoded⟩
                      rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
                      dsimp only
                      rw [opClass, fixClockDoEvalRes]
                      simp [doEvalRes, decoded, exhausted, timeoutError]
                  · right
                    refine ⟨short, ?_, finalForward _ (recordForward_trans _ _ _ ⟨firstForward, forwardMiddle⟩)⟩
                    rw [evaluate, (fixClockEvaluate _ _ args.reverse []).1, firstEqual]
end Flapjack.Compiler.Backend.SourceEval.Proofs
