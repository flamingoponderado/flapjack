import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateRecursive

/-! Expression cases of the source evaluator's oracle-adjustment induction. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL

/-- Variable-expression case of the source evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Var {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (name : Flapjack.NamespaceHOL.Ident ModN VarN) :
    ∀ (next : State F) (result : Result (List Value) Value),
      evaluate state env [.var name] = (next, result) ∧
      isInsertOracle ci f state.evalState ∧ result ≠ .err (.abort .typeError) →
      isInsertOracle ci f next.evalState ∧
        evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.var name] =
          ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  intro next result ⟨source, inserted, safe⟩
  cases lookup : Flapjack.NamespaceHOL.nsLookup env.v name with
  | none =>
    simp [evaluate, lookup, typeError] at source
    obtain ⟨_, rfl⟩ := source
    exact (safe rfl).elim
  | some value =>
    simp [evaluate, lookup] at source
    obtain ⟨rfl, rfl⟩ := source
    exact ⟨inserted, by simp [evaluate, lookup]⟩

/-- Recursive-function expression case of the source evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Letrec {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (funs : List (VarN × VarN × AstHOL.Exp)) (body : AstHOL.Exp)
    (ih : (funs.map (fun (name, _, _) => name)).Nodup →
      ExpsOracleAdjustedAt compile ci f state { env with v := buildRecEnv funs env env.v } [body]) :
    ExpsOracleAdjustedAt compile ci f state env [.letrec funs body] := by
  intro next result ⟨source, inserted, safe⟩
  classical
  by_cases unique : (funs.map (fun (name, _, _) => name)).Nodup
  · have bodyRun : evaluate state { env with v := buildRecEnv funs env env.v } [body] = (next, result) := by
      simpa [evaluate, unique] using source
    obtain ⟨nextInserted, replacement⟩ := ih unique next result ⟨bodyRun, inserted, safe⟩
    exact ⟨nextInserted, by simpa [evaluate, unique] using replacement⟩
  · simp [evaluate, unique, typeError] at source
    obtain ⟨_, rfl⟩ := source
    exact (safe rfl).elim

/-- Empty expression-list case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_ExpsNil {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) :
    ∀ (next : State F) (result : Result (List Value) Value),
      evaluate state env [] = (next, result) ∧
      isInsertOracle ci f state.evalState ∧ result ≠ .err (.abort .typeError) →
      isInsertOracle ci f next.evalState ∧
        evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [] =
          ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  intro next result ⟨source, inserted, _⟩
  simp [evaluate] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluate]⟩

/-- Literal case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Lit {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (lit : Lit) :
    ∀ (next : State F) (result : Result (List Value) Value),
      evaluate state env [.lit lit] = (next, result) ∧
      isInsertOracle ci f state.evalState ∧ result ≠ .err (.abort .typeError) →
      isInsertOracle ci f next.evalState ∧
        evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.lit lit] =
          ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  intro next result ⟨source, inserted, _⟩
  simp [evaluate] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluate]⟩

/-- Function-expression case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Fn {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (name : VarN) (body : AstHOL.Exp) :
    ∀ (next : State F) (result : Result (List Value) Value),
      evaluate state env [.fn name body] = (next, result) ∧
      isInsertOracle ci f state.evalState ∧ result ≠ .err (.abort .typeError) →
      isInsertOracle ci f next.evalState ∧
        evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.fn name body] =
          ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
  intro next result ⟨source, inserted, _⟩
  simp [evaluate] at source
  obtain ⟨rfl, rfl⟩ := source
  exact ⟨inserted, by simp [evaluate]⟩

/-- Type-annotation case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Tannot {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (typ : AstT)
    (ih : ExpsOracleAdjustedAt compile ci f state env [expr]) :
    ExpsOracleAdjustedAt compile ci f state env [.tannot expr typ] := by
  intro next result ⟨source, inserted, safe⟩
  have source' : evaluate state env [expr] = (next, result) := by simpa [evaluate] using source
  obtain ⟨nextInserted, replacement⟩ := ih next result ⟨source', inserted, safe⟩
  exact ⟨nextInserted, by simpa [evaluate] using replacement⟩

/-- Location-annotation case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Lannot {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (expr : AstHOL.Exp) (locs : Flapjack.Misc.Location.Locs)
    (ih : ExpsOracleAdjustedAt compile ci f state env [expr]) :
    ExpsOracleAdjustedAt compile ci f state env [.lannot expr locs] := by
  intro next result ⟨source, inserted, safe⟩
  have source' : evaluate state env [expr] = (next, result) := by simpa [evaluate] using source
  obtain ⟨nextInserted, replacement⟩ := ih next result ⟨source', inserted, safe⟩
  exact ⟨nextInserted, by simpa [evaluate] using replacement⟩

/-- Raise case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Raise {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (expr : AstHOL.Exp)
    (ih : ExpsOracleAdjustedAt compile ci f state env [expr]) :
    ExpsOracleAdjustedAt compile ci f state env [.raise expr] := by
  intro next result ⟨source, inserted, safe⟩
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
      obtain ⟨middleInserted, replacement⟩ := ih middle (.err error) ⟨run, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [evaluate, replacement]⟩
    | val values =>
      have pair : (middle, .err (.raise (headValue values))) = (next, result) := by
        simpa [evaluate, run] using source
      obtain ⟨middleInserted, replacement⟩ := ih middle (.val values) ⟨run, inserted, (by simp)⟩
      cases pair
      exact ⟨middleInserted, by simp [evaluate, replacement]⟩

/-- Let-expression case, using the induction hypotheses for the bound and
body expressions. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Let {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (name : Option VarN) (bound body : AstHOL.Exp)
    (state next : State F) (env : SemEnv Value)
    (boundIH : ExpsOracleAdjustedAt compile ci f state env [bound])
    (bodyIH : ∀ (middle : State F) (values : List Value), evaluate state env [bound] = (middle, .val values) →
      ExpsOracleAdjustedAt compile ci f middle
        { env with v := Flapjack.NamespaceHOL.nsOptBind name (headValue values) env.v } [body]) (result : Result (List Value) Value)
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
      obtain ⟨middleInserted, replacement⟩ := boundIH middle (.err error) ⟨run, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [adjusted, replacement]⟩
    | val values =>
      have bodyRun : evaluate middle { env with v := Flapjack.NamespaceHOL.nsOptBind name (headValue values) env.v } [body] =
          (next, result) := by simpa [run] using source
      obtain ⟨middleInserted, replacement⟩ := boundIH middle (.val values) ⟨run, inserted, (by simp)⟩
      obtain ⟨nextInserted, bodyReplacement⟩ := bodyIH middle values run next result ⟨bodyRun, middleInserted, safe⟩
      exact ⟨nextInserted, by simpa [adjusted, replacement] using bodyReplacement⟩

/-- Non-singleton expression-list case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_ExpsCons {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (first second : AstHOL.Exp) (rest : List AstHOL.Exp)
    (ih : (∀ (middle : State F) (outcome : Result (List Value) Value) (values : List Value),
      evaluate state env [first] = (middle, outcome) ∧ outcome = .val values →
        ExpsOracleAdjustedAt compile ci f middle env (second :: rest)) ∧
      ExpsOracleAdjustedAt compile ci f state env [first]) :
    ExpsOracleAdjustedAt compile ci f state env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro next result ⟨source, inserted, safe⟩
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
      obtain ⟨middleInserted, replacement⟩ := firstIH middle (.err error) ⟨run, inserted, innerSafe⟩
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
          obtain ⟨middleInserted, replacement⟩ := firstIH middle (.val values) ⟨run, inserted, (by simp)⟩
          obtain ⟨finalInserted, tailReplacement⟩ := tailIH middle (.val values) values ⟨run, rfl⟩ final (.err error) ⟨tailRun, middleInserted, tailSafe⟩
          cases pair
          exact ⟨finalInserted, by simp [adjusted, replacement, tailReplacement]⟩
        | val tailValues =>
          have pair : (final, .val (headValue values :: tailValues)) = (next, result) := by
            simpa [run, tailRun] using source
          obtain ⟨middleInserted, replacement⟩ := firstIH middle (.val values) ⟨run, inserted, (by simp)⟩
          obtain ⟨finalInserted, tailReplacement⟩ := tailIH middle (.val values) values ⟨run, rfl⟩ final (.val tailValues) ⟨tailRun, middleInserted, (by simp)⟩
          cases pair
          exact ⟨finalInserted, by simp [adjusted, replacement, tailReplacement]⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs
