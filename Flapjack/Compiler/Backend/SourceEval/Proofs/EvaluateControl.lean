import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateExpressions

/-! Control-flow cases of source evaluator oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Conditional-expression case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_If {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (condition yes no : AstHOL.Exp)
    (state next : State F) (env : SemEnv Value)
    (conditionIH : ExpsOracleAdjustedAt ci f compile state env [condition])
    (branchIH : ∀ (middle : State F) (values : List Value) (branch : AstHOL.Exp),
      evaluate state env [condition] = (middle, .val values) → doIf (headValue values) yes no = some branch →
      ExpsOracleAdjustedAt ci f compile middle env [branch]) (result : Result (List Value) Value)
    (source : evaluate state env [.if_ condition yes no] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.if_ condition yes no] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  let adjusted := { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
  simp only [evaluate, (fixClockEvaluate state env [condition] []).1] at source
  change isInsertOracle ci f next.evalState ∧
    evaluate adjusted env [.if_ condition yes no] =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)
  simp only [evaluate, (fixClockEvaluate adjusted env [condition] []).1]
  cases run : evaluate state env [condition] with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [run] using source
      have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := conditionIH middle (.err error) run inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := conditionIH middle (.val values) run inserted (by simp)
      simp only [run] at source
      cases chosen : doIf (headValue values) yes no with
      | none =>
        rw [chosen] at source
        simp [typeError] at source
        obtain ⟨_, rfl⟩ := source
        exact (safe rfl).elim
      | some branch =>
        rw [chosen] at source
        have branchRun : evaluate middle env [branch] = (next, result) := by simpa using source
        obtain ⟨nextInserted, branchReplacement⟩ :=
          branchIH middle values branch run chosen next result branchRun middleInserted safe
        refine ⟨nextInserted, ?_⟩
        rw [replacement]
        dsimp only
        rw [chosen]
        exact branchReplacement

/-- Short-circuit Boolean case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Log {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (op : Lop) (first second : AstHOL.Exp)
    (state next : State F) (env : SemEnv Value)
    (firstIH : ExpsOracleAdjustedAt ci f compile state env [first])
    (secondIH : ∀ (middle : State F) (values : List Value) (branch : AstHOL.Exp),
      evaluate state env [first] = (middle, .val values) → doLog op (headValue values) second = some (.exp branch) →
      ExpsOracleAdjustedAt ci f compile middle env [branch]) (result : Result (List Value) Value)
    (source : evaluate state env [.log op first second] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.log op first second] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  let adjusted := { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
  simp only [evaluate, (fixClockEvaluate state env [first] []).1] at source
  change isInsertOracle ci f next.evalState ∧
    evaluate adjusted env [.log op first second] =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)
  simp only [evaluate, (fixClockEvaluate adjusted env [first] []).1]
  cases run : evaluate state env [first] with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [run] using source
      have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := firstIH middle (.err error) run inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := firstIH middle (.val values) run inserted (by simp)
      simp only [run] at source
      cases selected : doLog op (headValue values) second with
      | none =>
        rw [selected] at source
        simp [typeError] at source
        obtain ⟨_, rfl⟩ := source
        exact (safe rfl).elim
      | some decision =>
        cases decision with
        | val value =>
          rw [selected] at source
          have pair : (middle, .val [value]) = (next, result) := by simpa using source
          cases pair
          refine ⟨middleInserted, ?_⟩
          rw [replacement]
          dsimp only
          rw [selected]
        | exp branch =>
          have branchEq : branch = second := doLog_selected op (headValue values) second branch selected
          subst branch
          rw [selected] at source
          have branchRun : evaluate middle env [second] = (next, result) := by simpa using source
          obtain ⟨nextInserted, branchReplacement⟩ := secondIH middle values second run selected next result branchRun middleInserted safe
          refine ⟨nextInserted, ?_⟩
          rw [replacement]
          dsimp only
          rw [selected]
          exact branchReplacement

/-- Constructor-expression case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Con {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (name : Option (Flapjack.NamespaceHOL.Ident ModN ConN)) (args : List AstHOL.Exp)
    (state next : State F) (env : SemEnv Value)
    (argsIH : doConCheck env.c name args.length = true → ExpsOracleAdjustedAt ci f compile state env args.reverse) (result : Result (List Value) Value)
    (source : evaluate state env [.con name args] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.con name args] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  by_cases check : doConCheck env.c name args.length = true
  · simp only [evaluate, check] at source ⊢
    cases run : evaluate state env args.reverse with
    | mk middle inner =>
      cases inner with
      | err error =>
        have pair : (middle, .err error) = (next, result) := by simpa [run] using source
        have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
          intro bad
          apply safe
          have h := congrArg Prod.snd pair
          simpa [bad] using h.symm
        obtain ⟨middleInserted, replacement⟩ := argsIH check middle (.err error) run inserted innerSafe
        cases pair
        exact ⟨middleInserted, by simp [replacement]⟩
      | val values =>
        obtain ⟨middleInserted, replacement⟩ := argsIH check middle (.val values) run inserted (by simp)
        cases built : buildConv env.c name values.reverse with
        | none =>
          simp [run, built, typeError] at source
          obtain ⟨_, rfl⟩ := source
          exact (safe rfl).elim
        | some value =>
          have pair : (middle, .val [value]) = (next, result) := by simpa [run, built] using source
          cases pair
          exact ⟨middleInserted, by simp [replacement, built]⟩
  · simp [evaluate, check, typeError] at source
    obtain ⟨_, rfl⟩ := source
    exact (safe rfl).elim

end Flapjack.Compiler.Backend.SourceEval.Proofs
