import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateRecursive

/-! Expression cases of the source evaluator's oracle-adjustment induction. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Empty expression-list case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_ExpsNil {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value)
    (source : evaluate state env [] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (_safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  simp [evaluate] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluate]⟩

/-- Literal case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Lit {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (lit : Lit) (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value)
    (source : evaluate state env [.lit lit] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (_safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.lit lit] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  simp [evaluate] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluate]⟩

/-- Function-expression case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Fn {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (name : VarN) (body : AstHOL.Exp) (state next : State F) (env : SemEnv Value)
    (result : Result (List Value) Value) (source : evaluate state env [.fn name body] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (_safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.fn name body] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  simp [evaluate] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluate]⟩

/-- Type-annotation case of the original evaluator induction. The recursive hypothesis here is stronger than the original fixed-state or conditionally selected induction hypothesis; this is Flapjack infrastructure and the faithful HOL case remains open. -/
theorem adjustOracle_evaluate_Tannot {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (expr : AstHOL.Exp) (typ : AstT) (ih : ExpsOracleAdjusted (F := F) ci f compile [expr])
    (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value)
    (source : evaluate state env [.tannot expr typ] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.tannot expr typ] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  have source' : evaluate state env [expr] = (next, result) := by simpa [evaluate] using source
  obtain ⟨nextInserted, replacement⟩ := ih state next env result source' inserted safe
  exact ⟨nextInserted, by simpa [evaluate] using replacement⟩

/-- Location-annotation case of the original evaluator induction. The recursive hypothesis here is stronger than the original fixed-state or conditionally selected induction hypothesis; this is Flapjack infrastructure and the faithful HOL case remains open. -/
theorem adjustOracle_evaluate_Lannot {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (expr : AstHOL.Exp) (locs : Flapjack.Misc.Location.Locs)
    (ih : ExpsOracleAdjusted (F := F) ci f compile [expr])
    (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value)
    (source : evaluate state env [.lannot expr locs] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.lannot expr locs] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  have source' : evaluate state env [expr] = (next, result) := by simpa [evaluate] using source
  obtain ⟨nextInserted, replacement⟩ := ih state next env result source' inserted safe
  exact ⟨nextInserted, by simpa [evaluate] using replacement⟩

/-- Raise case of the original evaluator induction. The recursive hypothesis here is stronger than the original fixed-state or conditionally selected induction hypothesis; this is Flapjack infrastructure and the faithful HOL case remains open. -/
theorem adjustOracle_evaluate_Raise {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (expr : AstHOL.Exp) (ih : ExpsOracleAdjusted (F := F) ci f compile [expr])
    (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value)
    (source : evaluate state env [.raise expr] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.raise expr] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  cases run : evaluate state env [expr] with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [evaluate, run] using source
      have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := ih state middle env (.err error) run inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [evaluate, replacement]⟩
    | val values =>
      have pair : (middle, .err (.raise (headValue values))) = (next, result) := by
        simpa [evaluate, run] using source
      obtain ⟨middleInserted, replacement⟩ := ih state middle env (.val values) run inserted (by simp)
      cases pair
      exact ⟨middleInserted, by simp [evaluate, replacement]⟩

/-- Let-expression case, using the induction hypotheses for the bound and
body expressions. The recursive hypothesis here is stronger than the original fixed-state or conditionally selected induction hypothesis; this is Flapjack infrastructure and the faithful HOL case remains open. -/
theorem adjustOracle_evaluate_Let {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (name : Option VarN) (bound body : AstHOL.Exp)
    (boundIH : ExpsOracleAdjusted (F := F) ci f compile [bound])
    (bodyIH : ExpsOracleAdjusted (F := F) ci f compile [body])
    (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value)
    (source : evaluate state env [.let_ name bound body] = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.let_ name bound body] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  let adjusted := { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
  simp only [evaluate, (fixClockEvaluate state env [bound] []).1] at source
  change isInsertOracle ci f next.evalState ∧
    evaluate adjusted env [.let_ name bound body] =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)
  simp only [evaluate, (fixClockEvaluate adjusted env [bound] []).1]
  cases run : evaluate state env [bound] with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [run] using source
      have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := boundIH state middle env (.err error) run inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      have bodyRun : evaluate middle { env with v := Flapjack.NamespaceHOL.nsOptBind name (headValue values) env.v } [body] =
          (next, result) := by simpa [run] using source
      obtain ⟨middleInserted, replacement⟩ := boundIH state middle env (.val values) run inserted (by simp)
      obtain ⟨nextInserted, bodyReplacement⟩ := bodyIH middle next _ result bodyRun middleInserted safe
      exact ⟨nextInserted, by simpa [adjusted, replacement] using bodyReplacement⟩

/-- Non-singleton expression-list case of the original evaluator induction. The recursive hypothesis here is stronger than the original fixed-state or conditionally selected induction hypothesis; this is Flapjack infrastructure and the faithful HOL case remains open. -/
theorem adjustOracle_evaluate_ExpsCons {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (firstIH : ExpsOracleAdjusted (F := F) ci f compile [first])
    (tailIH : ExpsOracleAdjusted (F := F) ci f compile (second :: rest))
    (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value)
    (source : evaluate state env (first :: second :: rest) = (next, result))
    (inserted : isInsertOracle ci f state.evalState) (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env (first :: second :: rest) =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  let adjusted := { state with evalState := adjustOracle ci (compile ∘ f) state.evalState }
  simp only [evaluate, (fixClockEvaluate state env [first] []).1] at source
  change isInsertOracle ci f next.evalState ∧
    evaluate adjusted env (first :: second :: rest) =
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
      obtain ⟨middleInserted, replacement⟩ := firstIH state middle env (.err error) run inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      cases tailRun : evaluate middle env (second :: rest) with
      | mk final tailResult =>
        cases tailResult with
        | err error =>
          have pair : (final, .err error) = (next, result) := by simpa [run, tailRun] using source
          have tailSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
            intro bad
            apply safe
            have h := congrArg Prod.snd pair
            simpa [bad] using h.symm
          obtain ⟨middleInserted, replacement⟩ := firstIH state middle env (.val values) run inserted (by simp)
          obtain ⟨finalInserted, tailReplacement⟩ := tailIH middle final env (.err error) tailRun middleInserted tailSafe
          cases pair
          exact ⟨finalInserted, by simp [adjusted, replacement, tailReplacement]⟩
        | val tailValues =>
          have pair : (final, .val (headValue values :: tailValues)) = (next, result) := by
            simpa [run, tailRun] using source
          obtain ⟨middleInserted, replacement⟩ := firstIH state middle env (.val values) run inserted (by simp)
          obtain ⟨finalInserted, tailReplacement⟩ := tailIH middle final env (.val tailValues) tailRun middleInserted (by simp)
          cases pair
          exact ⟨finalInserted, by simp [adjusted, replacement, tailReplacement]⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs
