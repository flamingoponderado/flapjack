module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateExpressions

@[expose] public section

/-! Control-flow cases of source evaluator oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Conditional-expression case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_If {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (condition yes no : AstHOL.Exp)
    (ih : (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value) (branch : AstHOL.Exp),
      evaluate state env [condition] = (middle, outcome) ∧ outcome = .val values ∧
        doIf (headValue values) yes no = some branch →
        ExpsOracleAdjustedAt compile ci f middle env [branch]) ∧
      ExpsOracleAdjustedAt compile ci f state env [condition]) :
    ExpsOracleAdjustedAt compile ci f state env [.if_ condition yes no] := by
  obtain ⟨branchIH, conditionIH⟩ := ih
  intro next result ⟨source, inserted, safe⟩
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
      obtain ⟨middleInserted, replacement⟩ := conditionIH middle (.err error) ⟨run, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := conditionIH middle (.val values) ⟨run, inserted, (by simp)⟩
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
          branchIH middle (.val values) values branch ⟨run, rfl, chosen⟩ next result ⟨branchRun, middleInserted, safe⟩
        refine ⟨nextInserted, ?_⟩
        rw [replacement]
        dsimp only
        rw [chosen]
        exact branchReplacement

/-- Short-circuit Boolean case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Log {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (op : Lop) (first second : AstHOL.Exp)
    (ih : (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value)
      (selection : ExpOrVal) (branch : AstHOL.Exp),
      evaluate state env [first] = (middle, outcome) ∧ outcome = .val values ∧
        doLog op (headValue values) second = some selection ∧ selection = .exp branch →
        ExpsOracleAdjustedAt compile ci f middle env [branch]) ∧
      ExpsOracleAdjustedAt compile ci f state env [first]) :
    ExpsOracleAdjustedAt compile ci f state env [.log op first second] := by
  obtain ⟨secondIH, firstIH⟩ := ih
  intro next result ⟨source, inserted, safe⟩
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
      obtain ⟨middleInserted, replacement⟩ := firstIH middle (.err error) ⟨run, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      obtain ⟨middleInserted, replacement⟩ := firstIH middle (.val values) ⟨run, inserted, (by simp)⟩
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
          obtain ⟨nextInserted, branchReplacement⟩ := secondIH middle (.val values) values (.exp second) second ⟨run, rfl, selected, rfl⟩ next result ⟨branchRun, middleInserted, safe⟩
          refine ⟨nextInserted, ?_⟩
          rw [replacement]
          dsimp only
          rw [selected]
          exact branchReplacement

/-- Constructor-expression case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Con {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (name : Option (Flapjack.NamespaceHOL.Ident ModN ConN)) (args : List AstHOL.Exp)
    (argsIH : doConCheck env.c name args.length = true →
      ExpsOracleAdjustedAt compile ci f state env args.reverse) :
    ExpsOracleAdjustedAt compile ci f state env [.con name args] := by
  intro next result ⟨source, inserted, safe⟩
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
        obtain ⟨middleInserted, replacement⟩ := argsIH check middle (.err error) ⟨run, inserted, innerSafe⟩
        cases pair
        exact ⟨middleInserted, by simp [replacement]⟩
      | val values =>
        obtain ⟨middleInserted, replacement⟩ := argsIH check middle (.val values) ⟨run, inserted, (by simp)⟩
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
