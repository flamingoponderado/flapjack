module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.InsertCorrectApp
public import Flapjack.EvaluateHOL.Induction

@[expose] public section

/-! Complete mutual oracle insertion correctness for the source evaluator. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL



/-- Inserting an agreeing, well-formed oracle preserves all three source evaluator
results except type errors. The evaluator inherits the rational-cut real assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "insert_oracle_correct"]
theorem insert_oracle_correct {Config F : Type} (ci : CompilerInstance Config) (oracle : EvalOracleFun) :
    (∀ (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp)
      (s' : State F) (res : Result (List Value) Value),
      evaluate s env exps = (s', res) ∧ isRecord ci s.evalState ∧ oracleAgrees oracle s'.evalState ∧
        oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧ res ≠ .err (.abort .typeError) →
      evaluate { s with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s.evalState } env exps =
        ({ s' with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s'.evalState }, res)) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (err : Value)
      (s' : State F) (res : Result (List Value) Value),
      evaluateMatch s env x rows err = (s', res) ∧ isRecord ci s.evalState ∧ oracleAgrees oracle s'.evalState ∧
        oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧ res ≠ .err (.abort .typeError) →
      evaluateMatch { s with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s.evalState } env x rows err =
        ({ s' with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s'.evalState }, res)) ∧
    (∀ (s : State F) (env : SemEnv Value) (decs : List Dec)
      (s' : State F) (res : Result (SemEnv Value) Value),
      evaluateDecs s env decs = (s', res) ∧ isRecord ci s.evalState ∧ oracleAgrees oracle s'.evalState ∧
        oracleExtendedWellFormed (mkCompilerFunFromCi ci) oracle ∧ res ≠ .err (.abort .typeError) →
      evaluateDecs { s with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s.evalState } env decs =
        ({ s' with evalState := insertGenOracle ci id (fun args => args.1.1) oracle s'.evalState }, res)) := by
  apply fullEvaluateInd (ExpsInsertAt ci oracle) (MatchInsertAt ci oracle) (DecsInsertAt ci oracle)
  exact ⟨insertOracleCorrect_ExpsNil ci oracle, insertOracleCorrect_ExpsCons ci oracle, insertOracleCorrect_Lit ci oracle,
    insertOracleCorrect_Raise ci oracle, insertOracleCorrect_Handle ci oracle, insertOracleCorrect_Con ci oracle,
    insertOracleCorrect_Var ci oracle, insertOracleCorrect_Fn ci oracle, insertOracleCorrect_App ci oracle,
    insertOracleCorrect_Log ci oracle, insertOracleCorrect_If ci oracle, insertOracleCorrect_Mat ci oracle,
    insertOracleCorrect_Let ci oracle, insertOracleCorrect_Letrec ci oracle, insertOracleCorrect_Tannot ci oracle,
    insertOracleCorrect_Lannot ci oracle, insertOracleCorrect_MatchNil ci oracle, insertOracleCorrect_MatchCons ci oracle,
    insertOracleCorrect_DecsNil ci oracle, insertOracleCorrect_DecsCons ci oracle, insertOracleCorrect_Dlet ci oracle,
    insertOracleCorrect_Dletrec ci oracle, insertOracleCorrect_Dtype ci oracle, insertOracleCorrect_Dtabbrev ci oracle,
    insertOracleCorrect_Denv ci oracle, insertOracleCorrect_Dexn ci oracle, insertOracleCorrect_Dmod ci oracle,
    insertOracleCorrect_Dlocal ci oracle⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs
