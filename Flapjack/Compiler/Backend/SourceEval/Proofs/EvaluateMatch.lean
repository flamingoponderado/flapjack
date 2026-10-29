import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateExpressions

/-! Pattern-match cases of source evaluator oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.NamespaceHOL

/-- Match-evaluation induction hypothesis for a fixed clause list. This
Flapjack predicate is proof infrastructure, not a separate HOL declaration. -/
def MatchOracleAdjusted {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (clauses : List (Pat × AstHOL.Exp)) : Prop :=
  ∀ (state next : State F) (env : SemEnv Value) (value errValue : Value)
    (result : Result (List Value) Value),
    evaluateMatch state env value clauses errValue = (next, result) →
    isInsertOracle ci f state.evalState → result ≠ .err (.abort .typeError) →
    isInsertOracle ci f next.evalState ∧
    evaluateMatch { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
      env value clauses errValue =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)

/-- Empty pattern-match case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_MatchNil {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (value errValue : Value)
    (result : Result (List Value) Value) (source : evaluateMatch state env value [] errValue = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (_safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateMatch { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env value [] errValue =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  simp [evaluateMatch] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluateMatch]⟩

/-- Nonempty pattern-match case, with induction hypotheses for the chosen
branch and for the remaining clauses. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_MatchCons {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (pat : Pat) (expr : AstHOL.Exp) (rest : List (Pat × AstHOL.Exp))
    (exprIH : ExpsOracleAdjusted (F := F) ci f compile [expr])
    (restIH : MatchOracleAdjusted (F := F) ci f compile rest)
    (state next : State F) (env : SemEnv Value) (value errValue : Value)
    (result : Result (List Value) Value)
    (source : evaluateMatch state env value ((pat, expr) :: rest) errValue = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateMatch { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
        env value ((pat, expr) :: rest) errValue =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  classical
  by_cases unique : (patBindings pat).Nodup
  · cases matched : pmatch env.c state.refs pat value [] with
    | noMatch =>
      have source' : evaluateMatch state env value rest errValue = (next, result) := by
        simpa [evaluateMatch, unique, matched] using source
      obtain ⟨nextInserted, replacement⟩ := restIH state next env value errValue result source' inserted safe
      exact ⟨nextInserted, by simpa [evaluateMatch, unique, matched] using replacement⟩
    | typeError =>
      simp [evaluateMatch, unique, matched, typeError] at source
      obtain ⟨_, rfl⟩ := source
      exact (safe rfl).elim
    | «match» bindings =>
      have source' : evaluate state { env with v := nsAppend (alistToNs bindings) env.v } [expr] =
          (next, result) := by simpa [evaluateMatch, unique, matched] using source
      obtain ⟨nextInserted, replacement⟩ := exprIH state next _ result source' inserted safe
      exact ⟨nextInserted, by simpa [evaluateMatch, unique, matched] using replacement⟩
  · simp [evaluateMatch, unique, typeError] at source
    obtain ⟨_, rfl⟩ := source
    exact (safe rfl).elim

/-- Case-expression case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Mat {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (expr : AstHOL.Exp) (clauses : List (Pat × AstHOL.Exp))
    (exprIH : ExpsOracleAdjusted (F := F) ci f compile [expr])
    (matchIH : MatchOracleAdjusted (F := F) ci f compile clauses)
    (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value)
    (source : evaluate state env [.mat expr clauses] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.mat expr clauses] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  let adjusted := { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
  simp only [evaluate, (fixClockEvaluate state env [expr] []).1] at source
  change isInsertOracle ci f next.evalState ∧
    evaluate adjusted env [.mat expr clauses] =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)
  simp only [evaluate, (fixClockEvaluate adjusted env [expr] []).1]
  cases run : evaluate state env [expr] with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [run] using source
      have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := exprIH state middle env (.err error) run inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      by_cases matchable : canPmatchAll env.c middle.refs (clauses.map Prod.fst) (headValue values) = true
      · have branch : evaluateMatch middle env (headValue values) clauses bindExnV = (next, result) := by
          simpa [run, matchable] using source
        obtain ⟨middleInserted, replacement⟩ := exprIH state middle env (.val values) run inserted (by simp)
        obtain ⟨nextInserted, branchReplacement⟩ :=
          matchIH middle next env (headValue values) bindExnV result branch middleInserted safe
        exact ⟨nextInserted, by simpa [adjusted, replacement, matchable] using branchReplacement⟩
      · simp [run, matchable, typeError] at source
        obtain ⟨_, rfl⟩ := source
        exact (safe rfl).elim

/-- Exception-handler case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Handle {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (expr : AstHOL.Exp) (clauses : List (Pat × AstHOL.Exp))
    (exprIH : ExpsOracleAdjusted (F := F) ci f compile [expr])
    (matchIH : MatchOracleAdjusted (F := F) ci f compile clauses)
    (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value)
    (source : evaluate state env [.handle expr clauses] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.handle expr clauses] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  let adjusted := { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
  simp only [evaluate, (fixClockEvaluate state env [expr] []).1] at source
  change isInsertOracle ci f next.evalState ∧
    evaluate adjusted env [.handle expr clauses] =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)
  simp only [evaluate, (fixClockEvaluate adjusted env [expr] []).1]
  cases run : evaluate state env [expr] with
  | mk middle inner =>
    cases inner with
    | val values =>
      have pair : (middle, .val values) = (next, result) := by simpa [run] using source
      obtain ⟨middleInserted, replacement⟩ := exprIH state middle env (.val values) run inserted (by simp)
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | err error =>
      cases error with
      | abort abort =>
        have pair : (middle, .err (.abort abort)) = (next, result) := by simpa [run] using source
        have innerSafe : (Result.err (.abort abort) : Result (List Value) Value) ≠ .err (.abort .typeError) := by
          intro bad
          apply safe
          have h := congrArg Prod.snd pair
          simpa [bad] using h.symm
        obtain ⟨middleInserted, replacement⟩ := exprIH state middle env (.err (.abort abort)) run inserted innerSafe
        cases pair
        exact ⟨middleInserted, by simp [adjusted, replacement]⟩
      | raise value =>
        by_cases matchable : canPmatchAll env.c middle.refs (clauses.map Prod.fst) value = true
        · have branch : evaluateMatch middle env value clauses value = (next, result) := by
            simpa [run, matchable] using source
          obtain ⟨middleInserted, replacement⟩ := exprIH state middle env (.err (.raise value)) run inserted (by simp)
          obtain ⟨nextInserted, branchReplacement⟩ :=
            matchIH middle next env value value result branch middleInserted safe
          exact ⟨nextInserted, by simpa [adjusted, replacement, matchable] using branchReplacement⟩
        · simp [run, matchable, typeError] at source
          obtain ⟨_, rfl⟩ := source
          exact (safe rfl).elim

end Flapjack.Compiler.Backend.SourceEval.Proofs
