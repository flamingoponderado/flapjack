module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.RecordForwardApp
public import Flapjack.EvaluateHOL.Induction

@[expose] public section

/-! Complete mutual recording-state preservation for the source evaluator. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL



/-- Source evaluation preserves recording state, extends the recorded oracle,
and preserves recorded-oracle well-formedness in all three evaluators. The
evaluator inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_is_record_forward"]
theorem evaluate_is_record_forward {Config F : Type} (ci : CompilerInstance Config) :
    (∀ (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp)
      (s' : State F) (res : Result (List Value) Value),
      evaluate s env exps = (s', res) ∧ isRecord ci s.evalState →
      isRecord ci s'.evalState ∧ recordForward s.evalState s'.evalState ∧
      (recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s.evalState).oracle →
        recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s'.evalState).oracle)) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value)
      (s' : State F) (res : Result (List Value) Value),
      evaluateMatch s env x rows err = (s', res) ∧ isRecord ci s.evalState →
      isRecord ci s'.evalState ∧ recordForward s.evalState s'.evalState ∧
      (recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s.evalState).oracle →
        recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s'.evalState).oracle)) ∧
    (∀ (s : State F) (env : SemEnv Value) (decs : List Dec)
      (s' : State F) (res : Result (SemEnv Value) Value),
      evaluateDecs s env decs = (s', res) ∧ isRecord ci s.evalState →
      isRecord ci s'.evalState ∧ recordForward s.evalState s'.evalState ∧
      (recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s.evalState).oracle →
        recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState s'.evalState).oracle)) := by
  apply fullEvaluateInd (ExpsRecordAt ci) (MatchRecordAt ci) (DecsRecordAt ci)
  exact ⟨evaluateIsRecordForward_ExpsNil ci, evaluateIsRecordForward_ExpsCons ci,
    evaluateIsRecordForward_Lit ci, evaluateIsRecordForward_Raise ci, evaluateIsRecordForward_Handle ci,
    evaluateIsRecordForward_Con ci, evaluateIsRecordForward_Var ci, evaluateIsRecordForward_Fn ci,
    evaluateIsRecordForward_App ci, evaluateIsRecordForward_Log ci, evaluateIsRecordForward_If ci,
    evaluateIsRecordForward_Mat ci, evaluateIsRecordForward_Let ci, evaluateIsRecordForward_Letrec ci,
    evaluateIsRecordForward_Tannot ci, evaluateIsRecordForward_Lannot ci, evaluateIsRecordForward_MatchNil ci,
    evaluateIsRecordForward_MatchCons ci, evaluateIsRecordForward_DecsNil ci, evaluateIsRecordForward_DecsCons ci,
    evaluateIsRecordForward_Dlet ci, evaluateIsRecordForward_Dletrec ci, evaluateIsRecordForward_Dtype ci,
    evaluateIsRecordForward_Dtabbrev ci, evaluateIsRecordForward_Denv ci, evaluateIsRecordForward_Dexn ci,
    evaluateIsRecordForward_Dmod ci, evaluateIsRecordForward_Dlocal ci⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs
