module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateApp
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateMatch
public import Flapjack.SemanticsHOL
public import Flapjack.EvaluateHOL.Induction

@[expose] public section

/-! Mutual lexicographic induction for source evaluator oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.NamespaceHOL
open Flapjack.SemanticsHOL


/-- The three original evaluator simulations under oracle adjustment. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjust_oracle_evaluate {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (preserves : ∀ (state : State F) (env : SemEnv Value) (decs : List Dec)
      (next : State F) (result : Result (SemEnv Value) Value),
      evaluateDecs state env decs = (next, result) ∧ result ≠ .err (.abort .typeError) →
      evaluateDecs state env (compile decs) = (next, result)) :
    (∀ (state : State F) (env : SemEnv Value) (exprs : List AstHOL.Exp)
      (next : State F) (result : Result (List Value) Value),
      evaluate state env exprs = (next, result) ∧ isInsertOracle ci f state.evalState ∧
        result ≠ .err (.abort .typeError) →
      isInsertOracle ci f next.evalState ∧
        evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env exprs =
          ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)) ∧
    (∀ (state : State F) (env : SemEnv Value) (value : Value) (clauses : List (Pat × AstHOL.Exp))
      (errValue : Value) (next : State F) (result : Result (List Value) Value),
      evaluateMatch state env value clauses errValue = (next, result) ∧
        isInsertOracle ci f state.evalState ∧ result ≠ .err (.abort .typeError) →
      isInsertOracle ci f next.evalState ∧
        evaluateMatch { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
          env value clauses errValue = ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)) ∧
    (∀ (state : State F) (env : SemEnv Value) (decs : List Dec)
      (next : State F) (result : Result (SemEnv Value) Value),
      evaluateDecs state env decs = (next, result) ∧ isInsertOracle ci f state.evalState ∧
        result ≠ .err (.abort .typeError) →
      isInsertOracle ci f next.evalState ∧
        evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env decs =
          ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)) := by
  apply fullEvaluateInd (ExpsOracleAdjustedAt compile ci f) (MatchOracleAdjustedAt compile ci f)
    (DecsOracleAdjustedAt compile ci f)
  exact ⟨adjustOracle_evaluate_ExpsNil compile ci f preserves, adjustOracle_evaluate_ExpsCons compile ci f preserves,
    adjustOracle_evaluate_Lit compile ci f preserves, adjustOracle_evaluate_Raise compile ci f preserves,
    adjustOracle_evaluate_Handle compile ci f preserves, adjustOracle_evaluate_Con compile ci f preserves,
    adjustOracle_evaluate_Var compile ci f preserves, adjustOracle_evaluate_Fn compile ci f preserves,
    adjustOracle_evaluate_App compile ci f preserves, adjustOracle_evaluate_Log compile ci f preserves,
    adjustOracle_evaluate_If compile ci f preserves, adjustOracle_evaluate_Mat compile ci f preserves,
    adjustOracle_evaluate_Let compile ci f preserves, adjustOracle_evaluate_Letrec compile ci f preserves,
    adjustOracle_evaluate_Tannot compile ci f preserves, adjustOracle_evaluate_Lannot compile ci f preserves,
    adjustOracle_evaluate_MatchNil compile ci f preserves, adjustOracle_evaluate_MatchCons compile ci f preserves,
    adjustOracle_evaluate_DecsNil compile ci f preserves, adjustOracle_evaluate_DecsCons compile ci f preserves,
    adjustOracle_evaluate_Dlet compile ci f preserves, adjustOracle_evaluate_Dletrec compile ci f preserves,
    adjustOracle_evaluate_Dtype compile ci f preserves, adjustOracle_evaluate_Dtabbrev compile ci f preserves,
    adjustOracle_evaluate_Denv compile ci f preserves, adjustOracle_evaluate_Dexn compile ci f preserves,
    adjustOracle_evaluate_Dmod compile ci f preserves, adjustOracle_evaluate_Dlocal compile ci f preserves⟩

/-- HOL's local specialization of the declaration component at a chosen clock. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_ev_decs"]
theorem adjust_oracle_ev_decs {Config F : Type} (compile : List Dec → List Dec)
    (state : State F) (clock : Nat) (ci : CompilerInstance Config) (f : List Dec → List Dec) :
    ∀ (env : SemEnv Value) (decs : List Dec) (next : State F)
      (result : Result (SemEnv Value) Value),
      (∀ (s : State F) (e : SemEnv Value) (ds : List Dec) (s' : State F)
        (res : Result (SemEnv Value) Value),
        evaluateDecs s e ds = (s', res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s e (compile ds) = (s', res)) →
      evaluateDecs { state with clock := clock } env decs = (next, result) ∧
        isInsertOracle ci f state.evalState ∧ result ≠ .err (.abort .typeError) →
      isInsertOracle ci f next.evalState ∧
        evaluateDecs { { state with clock := clock } with
          evalState := adjustOracle ci (compile ∘ f) state.evalState } env decs =
          ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  intro env decs next result preserves ⟨run, inserted, safe⟩
  exact (adjust_oracle_evaluate compile ci f preserves).2.2
    { state with clock := clock } env decs next result ⟨run, inserted, safe⟩

/-- Oracle adjustment preserves program observations under the original
declaration-compiler preservation and non-failure hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_semantics_prog"]
theorem adjust_oracle_semantics_prog {Config F : Type} (compile f : List Dec → List Dec)
    (ci : CompilerInstance Config)
    (preserves : ∀ (state : State F) (env : SemEnv Value) (decs : List Dec)
      (next : State F) (result : Result (SemEnv Value) Value),
      evaluateDecs state env decs = (next, result) ∧ result ≠ .err (.abort .typeError) →
      evaluateDecs state env (compile decs) = (next, result))
    (state : State F) (env : SemEnv Value) (program : List Dec) (outcome : HolBehaviour)
    (premises : isInsertOracle ci f state.evalState ∧
      ¬ Flapjack.SemanticsHOL.semanticsProg state env program .fail ∧
      Flapjack.SemanticsHOL.semanticsProg state env program outcome) :
    Flapjack.SemanticsHOL.semanticsProg
      { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env program outcome := by
  obtain ⟨inserted, noFail, source⟩ := premises
  have observations : ∀ clock,
      evaluateProgWithClock { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env clock program =
        evaluateProgWithClock state env clock program := by
    intro clock
    cases run : evaluateDecs { state with clock := clock } env program with
    | mk next result =>
      have safe : result ≠ .err (.abort .typeError) := by
        intro bad
        apply noFail
        change ∃ k, (evaluateProgWithClock state env k program).2 = .err (.abort .typeError)
        refine ⟨clock, ?_⟩
        simp [evaluateProgWithClock, run, bad]
      have target := (adjust_oracle_ev_decs compile state clock ci f env program next result
        preserves ⟨run, inserted, safe⟩).2
      simpa [evaluateProgWithClock, run] using congrArg (fun p => (p.1.ffi, p.2)) target
  cases outcome <;> simpa only [semanticsProg, observations] using source

end Flapjack.Compiler.Backend.SourceEval.Proofs
