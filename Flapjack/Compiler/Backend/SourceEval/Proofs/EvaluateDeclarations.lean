import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleSemantics

/-! Oracle adjustment cases for the source evaluator's declarations. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Declaration-compiler preservation assumption from the HOL induction. -/
def DeclarationCompilerPreserves {F : Type} (compile : List Dec → List Dec) : Prop :=
  ∀ (state next : State F) (env : SemEnv Value) (ds : List Dec)
    (result : Result (SemEnv Value) Value),
    evaluateDecs state env ds = (next, result) → result ≠ .err (.abort .typeError) →
    evaluateDecs state env (compile ds) = (next, result)

/-- Type-abbreviation declaration case of the source evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Dtabbrev {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (locs : Flapjack.Misc.Location.Locs)
    (vars : List TvarN) (name : TypeN) (typ : AstT) (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env [.dtabbrev locs vars name typ] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (_safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.dtabbrev locs vars name typ] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  simp [evaluateDecs] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluateDecs]⟩

/-- Datatype-declaration case of the source evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Dtype {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (locs : Flapjack.Misc.Location.Locs)
    (types : TypeDef) (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env [.dtype locs types] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.dtype locs types] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  by_cases check : types.all checkDupCtors = true
  · simp [evaluateDecs, check] at source
    obtain ⟨rfl, rfl⟩ := source
    exact ⟨inserted, by simp [evaluateDecs, check]⟩
  · simp [evaluateDecs, check, typeError] at source
    obtain ⟨_, rfl⟩ := source
    exact (safe rfl).elim

/-- Recursive value-declaration case of the source evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Dletrec {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (locs : Flapjack.Misc.Location.Locs)
    (funs : List (VarN × VarN × AstHOL.Exp)) (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env [.dletrec locs funs] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.dletrec locs funs] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  classical
  simp only [evaluateDecs] at source ⊢
  split at source
  · rename_i check
    simp only [Prod.mk.injEq] at source
    obtain ⟨rfl, rfl⟩ := source
    exact ⟨inserted, by simp [check]⟩
  · simp [typeError] at source
    obtain ⟨_, rfl⟩ := source
    exact (safe rfl).elim

/-- Empty declaration-list case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_DecsNil {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env [] = (next, result))
    (inserted : isInsertOracle ci f state.evalState)
    (_safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  simp [evaluateDecs] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluateDecs]⟩

/-- Exception-declaration case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Dexn {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (locs : Flapjack.Misc.Location.Locs) (name : ConN) (types : List AstT)
    (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env [.dexn locs name types] = (next, result))
    (inserted : isInsertOracle ci f state.evalState)
    (_safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.dexn locs name types] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  simp [evaluateDecs] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluateDecs]⟩

/-- The `Denv` case of the original evaluator induction. The declaration
compiler-preservation premise is retained from the complete HOL theorem; this
case itself only needs the environment bookkeeping lemmas. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Denv {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec)
    (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (name : TvarN)
    (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env [.denv name] = (next, result))
    (inserted : isInsertOracle ci f state.evalState)
    (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.denv name] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  cases declared : declareEnv state.evalState env with
  | none =>
    simp [evaluateDecs, declared, typeError] at source
    obtain ⟨_, rfl⟩ := source
    exact (safe rfl).elim
  | some pair =>
    obtain ⟨value, evalState⟩ := pair
    simp [evaluateDecs, declared] at source
    obtain ⟨rfl, rfl⟩ := source
    constructor
    · exact declareEnv_isInsert ci f _ env value evalState declared inserted
    · simp [evaluateDecs, declareEnv_adjust, declared]

end Flapjack.Compiler.Backend.SourceEval.Proofs
