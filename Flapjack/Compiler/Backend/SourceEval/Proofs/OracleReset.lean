import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleCallback
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleExtraction
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleRecording

/-! Interaction of source Eval oracle recording and generation reset. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_do_eval"]
theorem insert_doEval {Config : Type} (values : List Value) (es : Option EvalState)
    (env : SemEnv Value) (decs : List Flapjack.AstHOL.Dec) (es' : Option EvalState)
    (ci : CompilerInstance Config) (oracle : EvalOracleFun)
    (premises : doEval values es = some (env, decs, es') ∧ isRecord ci es) :
    isRecord ci es' ∧ recordForward es es' ∧
    (oracleAgrees oracle es' ∧ oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle →
      doEval values (insertGenOracle ci id (fun args => args.1.1) oracle es) =
        some (env, decs, insertGenOracle ci id (fun args => args.1.1) oracle es')) ∧
    (recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState es).oracle →
      recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState es').oracle) := by
  classical
  obtain ⟨evaluated, recording⟩ := premises
  rcases es with _ | ⟨s | s⟩
  · cases recording
  · cases recording
  · simp [isRecord] at recording
    simp only [doEval, recording] at evaluated
    cases callback : doEvalRecord ci values s.oracle with
    | none => simp [callback] at evaluated
    | some output =>
      obtain ⟨envId, newOracle, declarations⟩ := output
      cases lookup : lookupEnv s envId with
      | none => simp [callback, lookup] at evaluated
      | some foundEnv =>
        simp [callback, lookup] at evaluated
        obtain ⟨rfl, rfl, rfl⟩ := evaluated
        rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, tail⟩⟩⟩⟩⟩⟩ <;>
          try simp [doEvalRecord] at callback
        cases tail with
        | cons _ _ => simp at callback
        | nil =>
          cases idDecoded : valueToEnvId a with
          | none => simp [idDecoded] at callback
          | some idValue =>
            cases decDecoded : vFunAbs ci.decsDom ci.decsV c with
            | none => simp [idDecoded, decDecoded] at callback
            | some decValue =>
              by_cases valid : compilerAgrees (mkCompilerFunFromCi ci) (idValue, b, decValue) (d, e, f) ∧
                  b = (s.oracle 0).2.1
              · simp [idDecoded, decDecoded, valid] at callback
                obtain ⟨_, rfl, rfl, rfl⟩ := callback
                refine ⟨?_, ?_, ?_, ?_⟩
                · simp [isRecord, addEnvGeneration]
                · simp only [recordForward, addEnvGeneration]
                  refine ⟨_, rfl, ?_, ?_⟩
                  · simp
                  · intro j hj
                    simp [show j ≠ 0 by omega,
                      show j ≠ (s.oracle 0).1.1 + 1 by omega]
                · intro agreed
                  simp only [oracleAgrees, addEnvGeneration] at agreed
                  have event := agreed.1 (s.oracle 0).1.1 (by simp)
                  simp at event
                  cases compiled : mkCompilerFunFromCi ci (idValue, b, decValue) with
                  | none => simp [compilerAgrees, compiled] at valid
                  | some result =>
                    obtain ⟨nextState, byteList, wordList⟩ := result
                    cases byteDecoded : valueToWord8List e with
                    | none => simp [compilerAgrees, compiled, byteDecoded] at valid
                    | some decodedBytes =>
                      cases wordDecoded : valueToWord64List f with
                      | none => simp [compilerAgrees, compiled, byteDecoded, wordDecoded] at valid
                      | some decodedWords =>
                        have previous := valid.2
                        simp [compilerAgrees, compiled, byteDecoded, wordDecoded] at valid
                        have extended := agreed.2
                        unfold oracleExtendedWellFormed at extended
                        have future := extended (s.oracle 0).1.1 (nextState, byteList, wordList)
                          (by simpa [event, ← previous] using compiled)
                        have futureValue : d = (oracle (1 + (s.oracle 0).1.1)).2.1 := by
                          simpa [valid.1.1, Nat.add_comm] using future
                        simp only [lookupEnv] at lookup
                        simp [doEval, insertGenOracle, doEvalOracle, Flapjack.holShiftSeq,
                          addEnvGeneration, event, ← previous, compiled, byteDecoded, wordDecoded,
                          valid.1.1, valid.1.2.1, valid.1.2.2.1, futureValue, lookupEnv, lookup,
                          Nat.add_comm]
                        funext j
                        simp [Flapjack.holShiftSeq, Nat.add_assoc]
                · intro wf
                  have step := recordedOracleWellFormed_step (mkCompilerFunFromCi ci) s.oracle
                    (idValue, b, decValue) d e f ⟨wf, valid.1, fun _ => valid.2⟩
                  simpa [oracleState, addEnvGeneration, valid.2] using step
              · simp [idDecoded, decDecoded, valid] at callback

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "reset_env_generation_orac_eqs"]
theorem resetEnvGeneration_oracleEqs {Config : Type} (ci : CompilerInstance Config)
    (es₂ es₃ es₁ : Option EvalState) (oracle : EvalOracleFun) :
    (isRecord ci (resetEnvGeneration es₂ es₃) ↔ isRecord ci es₃) ∧
    (recordForward es₁ (resetEnvGeneration es₂ es₃) ↔ recordForward es₁ es₃) ∧
    (oracleAgrees oracle (resetEnvGeneration es₂ es₃) ↔ oracleAgrees oracle es₃) ∧
    (resetEnvGeneration (insertGenOracle ci id (fun args => args.1.1) oracle es₁) es₂ =
      resetEnvGeneration es₁ es₂) ∧
    (resetEnvGeneration es₁ (insertGenOracle ci id (fun args => args.1.1) oracle es₂) =
      insertGenOracle ci id (fun args => args.1.1) oracle (resetEnvGeneration es₁ es₂)) ∧
    (oracleState (resetEnvGeneration es₂ es₃)).oracle = (oracleState es₃).oracle := by
  rcases es₁ with _ | ⟨_ | _⟩ <;>
    rcases es₂ with _ | ⟨_ | _⟩ <;>
    rcases es₃ with _ | ⟨_ | _⟩ <;>
    simp [resetEnvGeneration, insertGenOracle, isRecord, recordForward, oracleAgrees, oracleState]

@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_declare_env"]
theorem insert_declareEnv {Config : Type} (es₁ : Option EvalState) (env : SemEnv Value)
    (value : Value) (es₂ : Option EvalState) (ci : CompilerInstance Config) (oracle : EvalOracleFun)
    (premises : declareEnv es₁ env = some (value, es₂) ∧ isRecord ci es₁) :
    isRecord ci es₂ ∧ recordForward es₁ es₂ ∧
    (oracleAgrees oracle es₂ →
      declareEnv (insertGenOracle ci id (fun args => args.1.1) oracle es₁) env =
        some (value, insertGenOracle ci id (fun args => args.1.1) oracle es₂)) ∧
    (recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState es₁).oracle →
      recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState es₂).oracle) := by
  obtain ⟨declared, recording⟩ := premises
  rcases es₁ with _ | ⟨s | s⟩
  · cases recording
  · cases recording
  · cases found : s.envs[s.generation]? with
    | none => simp [declareEnv, found] at declared
    | some prior =>
      simp [declareEnv, found] at declared
      obtain ⟨rfl, rfl⟩ := declared
      simp [isRecord] at recording
      simp [isRecord, recordForward, oracleAgrees, declareEnv, insertGenOracle,
        oracleState, found, recording]

end Flapjack.Compiler.Backend.SourceEval.Proofs
