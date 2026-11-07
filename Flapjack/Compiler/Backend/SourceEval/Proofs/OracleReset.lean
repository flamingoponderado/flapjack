import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleCallback
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleExtraction
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleRecording

/-! Interaction of source Eval oracle recording and generation reset. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL

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
