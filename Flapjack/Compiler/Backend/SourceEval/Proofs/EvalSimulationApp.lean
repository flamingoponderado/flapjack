module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDeclarations
public import Flapjack.Compiler.Backend.SourceEval.Proofs.DoAppSimulation
public import Flapjack.Compiler.Backend.SourceEval.Proofs.DoEvalSimulation
public import Flapjack.Compiler.Backend.SourceEval.Proofs.DeclareEnvSimulation
public import Flapjack.Compiler.Backend.SourceEval.Proofs.SimulationPrerequisites
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentAppend

@[expose] public section

/-! Application case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Application preserves the complete source evaluator simulation. The four
induction hypotheses retain the original pair and result binders and guards.
The evaluator inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_App {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (op : Op) (args : List Flapjack.AstHOL.Exp)
    (ih :
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (pair : SemEnv Value × Flapjack.AstHOL.Exp) (callEnv : SemEnv Value) (body : Flapjack.AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .funApp ∧ doOpApp values.reverse = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → ExpsSimAt ci (decClock middle) callEnv [body]) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (decoded : State F) (decodedResult : Result (SemEnv Value × List Dec) Value)
          (pair : SemEnv Value × List Dec) (evalEnv : SemEnv Value) (decs : List Dec),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .evalOp ∧ doEvalRes values.reverse middle = (decoded, decodedResult) ∧
        decodedResult = .val pair ∧ pair = (evalEnv, decs) ∧ decoded.clock ≠ 0 →
        DecsSimAt ci (decClock decoded) evalEnv decs) ∧
      (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
          (mode : ThunkMode) (thunk : Value) (pair : SemEnv Value × Flapjack.AstHOL.Exp)
          (callEnv : SemEnv Value) (body : Flapjack.AstHOL.Exp),
        evaluate s env args.reverse = (middle, outcome) ∧ outcome = .val values ∧
        getOpClass op = .force ∧ destThunk values.reverse middle.refs = .isThunk mode thunk ∧
        mode = .notEvaluated ∧ doOpApp [thunk, .conv none []] = some pair ∧
        pair = (callEnv, body) ∧ middle.clock ≠ 0 → ExpsSimAt ci (decClock middle) callEnv [body]) ∧
      ExpsSimAt ci s env args.reverse) :
    ExpsSimAt ci s env [.app op args] := by
  obtain ⟨callIH, evalIH, forceIH, argsIH⟩ := ih
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  rw [evaluate, (fixClockEvaluate s env args.reverse []).1] at run
  cases argsRun : evaluate s env args.reverse with
  | mk middle argResult =>
    cases argResult with
    | err error =>
      simp only [argsRun] at run
      cases run
      have argsSafe : Result.err error ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        argsIH s' (.err error) t env' ⟨argsRun, related, envRelated, argsSafe⟩
      cases r₁ with
      | val values => cases resultRel₁
      | err targetErr =>
        refine ⟨es₁, t₁, .err targetErr, ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
    | val values =>
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd₁, stack₁⟩ :=
        argsIH middle (.val values) t env' ⟨argsRun, related, envRelated, by simp⟩
      cases r₁ with
      | err error => cases resultRel₁
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRel es₁) values targetValues := resultRel₁
        simp only [argsRun] at run
        cases opClass : getOpClass op with
        | funApp =>
          rw [opClass] at run
          cases app : doOpApp values.reverse with
          | none =>
            simp [app, typeError] at run
            obtain ⟨_, rfl⟩ := run
            exact (safe rfl).elim
          | some pair =>
            rcases pair with ⟨callEnv, body⟩
            simp only [app] at run
            have valuesRev : List.Forall₂ (ValueRel es₁) values.reverse targetValues.reverse :=
              (List.forall₂_reverse_iff).2 valuesRel
            obtain ⟨callEnv', targetApp, callEnvRel⟩ :=
              doOpApp_related es₁ values.reverse targetValues.reverse callEnv body valuesRev app
            have ⟨clockEq, decRel⟩ := stateRel_clock ci middle t₁ stateRel₁
            by_cases clockZero : middle.clock = 0
            · simp [clockZero, timeoutError] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨es₁, t₁, .err (.abort .timeoutError), ?_, stateRel₁, esEq, ?_, fwd₁, ?_⟩
              · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                simp [opClass, targetApp, ← clockEq, clockZero, timeoutError]
              · simp [Flapjack.SemanticPrimitivesProps.resultRel, excRel]
              · intro notAbort
                simp [abort] at notAbort
            · simp [clockZero] at run
              have targetClock : t₁.clock ≠ 0 := by simpa [← clockEq] using clockZero
              obtain ⟨es₂, t₂, r₂, targetCall, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                callIH middle (.val values) values (callEnv, body) callEnv body
                  ⟨argsRun, rfl, opClass, app, rfl, clockZero⟩ s' res (decClock t₁) callEnv'
                  ⟨run, decRel, by simpa [esEq, decClock] using callEnvRel, safe⟩
              refine ⟨es₂, t₂, r₂, ?_, stateRel₂, esEq₂, resultRel₂, ?_, ?_⟩
              · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                simp [opClass, targetApp, targetClock, targetCall]
              · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq, decClock] using fwd₂⟩
              · intro notAbort
                exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq, decClock] using stack₂ notAbort⟩
        | force =>
          rw [opClass] at run
          have stores : List.Forall₂ (storeValueRel (ValueRel es₁)) middle.refs t₁.refs := by
            obtain ⟨dec, oracle, refs, rfl, stores, rest⟩ := stateRel₁
            simpa [esEq, oracleState] using stores
          have inspection : destRel es₁ (destThunk values.reverse middle.refs)
              (destThunk targetValues.reverse t₁.refs) := by
            have vals := (List.forall₂_reverse_iff).2 valuesRel
            generalize values.reverse = sourceValues at vals ⊢
            generalize targetValues.reverse = destValues at vals ⊢
            cases vals with
            | nil => simp [destThunk, destRel]
            | @cons v w vs ws head tail =>
              cases tail with
              | nil => exact destRelated es₁ middle.refs t₁.refs v w stores head
              | cons head tail => simp [destThunk, destRel]
          cases thunk : destThunk values.reverse middle.refs with
          | badRef | notThunk =>
            simp [thunk, typeError] at run
            obtain ⟨_, rfl⟩ := run
            exact (safe rfl).elim
          | isThunk mode value =>
            cases targetThunk : destThunk targetValues.reverse t₁.refs with
            | badRef | notThunk => simp [thunk, targetThunk, destRel] at inspection
            | isThunk targetMode targetValue =>
              simp only [thunk, targetThunk, destRel] at inspection
              obtain ⟨rfl, valueRel⟩ := inspection
              cases mode with
              | evaluated =>
                simp [thunk] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨es₁, t₁, .val [targetValue], ?_, stateRel₁, esEq, ?_, fwd₁, ?_⟩
                · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                  simp [opClass, targetThunk]
                · exact .cons valueRel .nil
                · intro _
                  exact stack₁ (by simp [abort])
              | notEvaluated =>
                simp only [thunk] at run
                cases app : doOpApp [value, .conv none []] with
                | none =>
                  simp [app, typeError] at run
                  obtain ⟨_, rfl⟩ := run
                  exact (safe rfl).elim
                | some pair =>
                  rcases pair with ⟨callEnv, body⟩
                  simp only [app] at run
                  have argRel : List.Forall₂ (ValueRel es₁) [value, .conv none []]
                      [targetValue, .conv none []] := .cons valueRel (.cons (.con .nil) .nil)
                  obtain ⟨callEnv', targetApp, callEnvRel⟩ :=
                    doOpApp_related es₁ _ _ callEnv body argRel app
                  have ⟨clockEq, decRel⟩ := stateRel_clock ci middle t₁ stateRel₁
                  by_cases clockZero : middle.clock = 0
                  · simp [clockZero, timeoutError] at run
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨es₁, t₁, .err (.abort .timeoutError), ?_, stateRel₁, esEq, ?_, fwd₁, ?_⟩
                    · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                      simp [opClass, targetThunk, targetApp, ← clockEq, clockZero, timeoutError]
                    · simp [Flapjack.SemanticPrimitivesProps.resultRel, excRel]
                    · intro notAbort
                      simp [abort] at notAbort
                  · simp only [clockZero, ↓reduceIte] at run
                    have targetClock : t₁.clock ≠ 0 := by simpa [← clockEq] using clockZero
                    cases callRun : evaluate (decClock middle) callEnv [body] with
                    | mk after result =>
                      cases result with
                      | err error =>
                        simp only [callRun] at run
                        cases run
                        obtain ⟨es₂, t₂, r₂, targetCall, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                          forceIH middle (.val values) values .notEvaluated value (callEnv, body) callEnv body
                            ⟨argsRun, rfl, opClass, thunk, rfl, app, rfl,
                              clockZero⟩ s' (.err error) (decClock t₁) callEnv'
                            ⟨callRun, decRel, by simpa [esEq, decClock] using callEnvRel, safe⟩
                        cases r₂ with
                        | val vals => cases resultRel₂
                        | err err' =>
                          refine ⟨es₂, t₂, .err err', ?_, stateRel₂, esEq₂, resultRel₂, ?_, ?_⟩
                          · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                            simp [opClass, targetThunk, targetApp, targetClock, targetCall]
                          · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq, decClock] using fwd₂⟩
                          · intro notAbort
                            exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq, decClock] using stack₂ notAbort⟩
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
                          obtain ⟨es₂, t₂, r₂, targetCall, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                            forceIH middle (.val values) values .notEvaluated value (callEnv, body) callEnv body
                              ⟨argsRun, rfl, opClass, thunk, rfl, app, rfl, clockZero⟩
                              after (.val newValues) (decClock t₁) callEnv'
                              ⟨callRun, decRel, by simpa [esEq, decClock] using callEnvRel, by simp⟩
                          cases r₂ with
                          | err error => cases resultRel₂
                          | val newValues' =>
                            have targetsRelated : List.Forall₂ (ValueRel es₂) values.reverse targetValues.reverse := by
                              apply (forwardRules es₁ value targetValue es₂ values.reverse targetValues.reverse env env').2.1
                              exact ⟨(List.forall₂_reverse_iff).2 valuesRel, by simpa [esEq, decClock] using fwd₂⟩
                            have stores₂ : List.Forall₂ (storeValueRel (ValueRel es₂)) after.refs t₂.refs := by
                              obtain ⟨dec, oracle, oldRefs, rfl, storeRel, rest⟩ := stateRel₂
                              simpa [esEq₂, oracleState] using storeRel
                            obtain ⟨refs', targetUpdate, updatedRel⟩ :=
                              updateThunk_related es₂ after.refs t₂.refs values.reverse targetValues.reverse
                                newValues newValues' refs stores₂ targetsRelated resultRel₂ updated
                            refine ⟨es₂, { t₂ with refs := refs' }, .val newValues', ?_, ?_, ?_, resultRel₂, ?_, ?_⟩
                            · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                              simp [opClass, targetThunk, targetApp, targetClock, targetCall, targetUpdate]
                            · obtain ⟨dec, oracle, oldRefs, targetEq, _, sourceEq, callback, rest⟩ := stateRel₂
                              subst t₂
                              simp [oracleState] at esEq₂
                              subst es₂
                              exact ⟨dec, oracle, refs', rfl, updatedRel, sourceEq, callback, rest⟩
                            · simpa using esEq₂
                            · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq, decClock] using fwd₂⟩
                            · intro notAbort
                              exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq, decClock] using stack₂ notAbort⟩
        | evalOp =>
          rw [opClass, fixClockDoEvalRes] at run
          cases decoded : doEval values.reverse middle.evalState with
          | none =>
            simp [doEvalRes, decoded] at run
            obtain ⟨_, rfl⟩ := run
            exact (safe rfl).elim
          | some data =>
            rcases data with ⟨evalEnv, decs, evalState⟩
            simp only [doEvalRes, decoded] at run
            have relatedValues : List.Forall₂ (ValueRel (oracleState t₁.evalState)) values targetValues := by
              simpa [esEq] using valuesRel
            obtain ⟨evalEnv', evalState', evalFwd, targetDecoded, evalEnvRel, decodedRel, resetRel⟩ :=
              doEval_sim values middle evalEnv decs evalState ci t₁ targetValues
                ⟨decoded, stateRel₁, relatedValues⟩
            have ⟨clockEq, decRel⟩ := stateRel_clock ci _ _ decodedRel
            by_cases clockZero : middle.clock = 0
            · simp [clockZero, timeoutError] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨oracleState evalState', { t₁ with evalState := evalState' }, .err (.abort .timeoutError),
                ?_, by simpa [clockZero] using decodedRel, rfl, ?_, ?_, ?_⟩
              · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                dsimp only
                rw [opClass, fixClockDoEvalRes]
                simp [doEvalRes, targetDecoded, ← clockEq, clockZero, timeoutError]
              · simp [Flapjack.SemanticPrimitivesProps.resultRel, excRel]
              · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq] using evalFwd⟩
              · intro notAbort
                simp [abort] at notAbort
            · simp only [clockZero, ↓reduceIte, (fixClockEvaluate _ _ [] _).2] at run
              have targetClock : t₁.clock ≠ 0 := by simpa using clockEq ▸ clockZero
              have decIH := evalIH middle (.val values) values { middle with evalState := evalState }
                (.val (evalEnv, decs)) (evalEnv, decs) evalEnv decs
                ⟨argsRun, rfl, opClass, by simp [doEvalRes, decoded], rfl, rfl, clockZero⟩
              cases decRun : evaluateDecs (decClock { middle with evalState := evalState }) evalEnv decs with
              | mk after decResult =>
                cases decResult with
                | err error =>
                  cases error with
                  | abort error =>
                    simp only [decRun] at run
                    cases run
                    obtain ⟨es₂, t₂, r₂, targetDec, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                      decIH s' (.err (.abort error)) (decClock { t₁ with evalState := evalState' }) evalEnv'
                        ⟨decRun, decRel, by simpa [decClock] using evalEnvRel, by intro h; apply safe; cases h; rfl⟩
                    cases r₂ with
                    | val val' => cases resultRel₂
                    | err err' =>
                      cases err' with
                      | raise v => cases resultRel₂
                      | abort error' =>
                        refine ⟨es₂, t₂, .err (.abort error'), ?_, stateRel₂, esEq₂, resultRel₂, ?_, ?_⟩
                        · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                          dsimp only
                          rw [opClass, fixClockDoEvalRes]
                          simp only [doEvalRes, targetDecoded, targetClock, ↓reduceIte]
                          rw [(fixClockEvaluate _ _ [] _).2, targetDec]
                        · apply envStoreForward_trans _ es₁ _
                          refine ⟨fwd₁, ?_⟩
                          exact envStoreForward_trans _ _ _ ⟨by simpa [esEq] using evalFwd, by simpa [decClock] using fwd₂⟩
                        · intro notAbort
                          simp [abort] at notAbort
                  | raise value =>
                    simp only [decRun] at run
                    cases run
                    obtain ⟨es₂, t₂, r₂, targetDec, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                      decIH after (.err (.raise value)) (decClock { t₁ with evalState := evalState' }) evalEnv'
                        ⟨decRun, decRel, by simpa [decClock] using evalEnvRel, by simp⟩
                    cases r₂ with
                    | val val' => cases resultRel₂
                    | err err' =>
                      cases err' with
                      | abort error' => cases resultRel₂
                      | raise targetValue =>
                        have stackDec : envStackForward (oracleState evalState') (oracleState t₂.evalState) := by
                          simpa [decClock, esEq₂] using stack₂ (by simp [abort])
                        obtain ⟨resetFwd, resetState, resetStack⟩ := resetRel after t₂
                          ⟨stateRel₂, by simpa [decClock, esEq₂] using fwd₂, stackDec⟩
                        refine ⟨oracleState (resetEnvGeneration t₁.evalState t₂.evalState),
                          { t₂ with evalState := resetEnvGeneration t₁.evalState t₂.evalState },
                          .err (.raise targetValue), ?_, resetState, rfl, ?_, ?_, ?_⟩
                        · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                          dsimp only
                          rw [opClass, fixClockDoEvalRes]
                          simp only [doEvalRes, targetDecoded, targetClock, ↓reduceIte]
                          rw [(fixClockEvaluate _ _ [] _).2, targetDec]
                        · change ValueRel _ value targetValue
                          apply valueRel_forward es₂ _ value targetValue resultRel₂
                          simpa [esEq₂] using resetFwd
                        · apply envStoreForward_trans _ es₁ _
                          refine ⟨fwd₁, ?_⟩
                          apply envStoreForward_trans _ (oracleState evalState') _
                          refine ⟨by simpa [esEq] using evalFwd, ?_⟩
                          exact envStoreForward_trans _ _ _ ⟨by simpa [decClock] using fwd₂, by simpa [esEq₂] using resetFwd⟩
                        · intro _
                          exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq] using resetStack⟩
                | val newEnv =>
                  simp only [decRun] at run
                  cases declared : declareEnv after.evalState (extendDecEnv newEnv evalEnv) with
                  | none =>
                    simp [declared, typeError] at run
                    obtain ⟨_, rfl⟩ := run
                    exact (safe rfl).elim
                  | some declaration =>
                    rcases declaration with ⟨value, finalEvalState⟩
                    simp only [declared] at run
                    cases run
                    obtain ⟨es₂, t₂, r₂, targetDec, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                      decIH after (.val newEnv) (decClock { t₁ with evalState := evalState' }) evalEnv'
                        ⟨decRun, decRel, by simpa [decClock] using evalEnvRel, by simp⟩
                    cases r₂ with
                    | err error => cases resultRel₂
                    | val newEnv' =>
                      change envRel (ValueRel es₂) newEnv newEnv' at resultRel₂
                      have evalEnvRel₂ : envRel (ValueRel es₂) evalEnv evalEnv' := by
                        apply (forwardRules (oracleState evalState') (.conv none []) (.conv none []) es₂ [] [] evalEnv evalEnv').2.2.1
                        exact ⟨evalEnvRel, by simpa [decClock] using fwd₂⟩
                      have finalEnvRel : envRel (ValueRel (oracleState t₂.evalState))
                          (extendDecEnv newEnv evalEnv) (extendDecEnv newEnv' evalEnv') := by
                        apply envRel_extendDecEnv
                        exact ⟨by simpa [esEq₂] using resultRel₂, by simpa [esEq₂] using evalEnvRel₂⟩
                      obtain ⟨value', finalEvalState', declaredFwd, targetDeclared, valueRel, declaredRel, declaredStack⟩ :=
                        declareEnv_sim after (extendDecEnv newEnv evalEnv) value finalEvalState ci t₂
                          (extendDecEnv newEnv' evalEnv') ⟨declared, stateRel₂, finalEnvRel⟩
                      have decFwd : envStoreForward (oracleState evalState') (oracleState t₂.evalState) := by
                        simpa [decClock, esEq₂] using fwd₂
                      have decStack : envStackForward (oracleState evalState') (oracleState t₂.evalState) := by
                        simpa [decClock, esEq₂] using stack₂ (by simp [abort])
                      obtain ⟨resetFwd, resetState, resetStack⟩ :=
                        resetRel { after with evalState := finalEvalState } { t₂ with evalState := finalEvalState' }
                          ⟨declaredRel, envStoreForward_trans _ _ _ ⟨decFwd, declaredFwd⟩,
                            envStackForward_trans _ _ _ ⟨decStack, declaredStack⟩⟩
                      refine ⟨oracleState (resetEnvGeneration t₁.evalState finalEvalState'),
                        { t₂ with evalState := resetEnvGeneration t₁.evalState finalEvalState' }, .val [value'],
                        ?_, resetState, rfl, ?_, ?_, ?_⟩
                      · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
                        dsimp only
                        rw [opClass, fixClockDoEvalRes]
                        simp only [doEvalRes, targetDecoded, targetClock, ↓reduceIte]
                        rw [(fixClockEvaluate _ _ [] _).2, targetDec]
                        simp [targetDeclared]
                      · exact .cons (valueRel_forward _ _ _ _ valueRel resetFwd) .nil
                      · apply envStoreForward_trans _ es₁ _
                        refine ⟨fwd₁, ?_⟩
                        apply envStoreForward_trans _ (oracleState evalState') _
                        refine ⟨by simpa [esEq] using evalFwd, ?_⟩
                        exact envStoreForward_trans _ _ _ ⟨decFwd, envStoreForward_trans _ _ _ ⟨declaredFwd, resetFwd⟩⟩
                      · intro _
                        exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq] using resetStack⟩
        | simple =>
          rw [opClass] at run
          cases app : doApp (middle.refs, middle.ffi) op values.reverse with
          | none =>
            simp [app, typeError] at run
            obtain ⟨_, rfl⟩ := run
            exact (safe rfl).elim
          | some outcome =>
            rcases outcome with ⟨⟨refs, ffi⟩, result⟩
            simp only [app] at run
            cases run
            have resultSafe : result ≠ .err (.abort .typeError) := by
              cases result <;> simp_all [listResult]
            have relatedValues : List.Forall₂ (ValueRel (oracleState t₁.evalState)) values targetValues := by
              simpa [esEq] using valuesRel
            obtain ⟨refs', result', oracle', oracleEq, targetApp, storesRel, resultRel⟩ :=
              doApp_sim middle op values refs ffi result ci t₁ targetValues
                ⟨app, stateRel₁, relatedValues, resultSafe⟩
            refine ⟨oracle', { t₁ with refs := refs', ffi := ffi }, listResult result', ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [evaluate, (fixClockEvaluate t env' args.reverse []).1, targetRun]
              simp [opClass, targetApp]
            · obtain ⟨dec, oracle, oldRefs, targetEq, _, sourceEq, callback, rest⟩ := stateRel₁
              subst t₁
              simp [oracleState] at oracleEq
              subst oracle'
              exact ⟨dec, oracle, refs', rfl, storesRel, sourceEq, callback, rest⟩
            · simpa using oracleEq
            · cases result <;> cases result' <;> simp_all [listResult, Flapjack.SemanticPrimitivesProps.resultRel]
            · simpa [esEq, oracleEq] using fwd₁
            · intro _
              simpa [esEq, oracleEq] using stack₁ (by simp [abort])
end Flapjack.Compiler.Backend.SourceEval.Proofs
