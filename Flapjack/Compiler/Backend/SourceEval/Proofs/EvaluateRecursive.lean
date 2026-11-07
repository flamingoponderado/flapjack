import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateDeclarations
import Flapjack.EvaluateProps.Declarations

/-! Recursive declaration cases of source evaluator oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.EvaluateProps

/-- Declaration adjustment at one input state and environment. This
Flapjack predicate allows the Eval case to use its clock-bounded induction
hypothesis without requiring a theorem for every input state. -/
def DecsOracleAdjustedAt {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec) (state : State F) (env : SemEnv Value) (program : List Dec) : Prop :=
  ∀ (next : State F) (result : Result (SemEnv Value) Value),
    evaluateDecs state env program = (next, result) ∧
    isInsertOracle ci f state.evalState ∧ result ≠ .err (.abort .typeError) →
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env program =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)

/-- Expression adjustment at a fixed input state and environment. This
Flapjack predicate represents the hypothesis for one recursive evaluation. -/
def ExpsOracleAdjustedAt {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec) (state : State F) (env : SemEnv Value)
    (expressions : List AstHOL.Exp) : Prop :=
  ∀ (next : State F) (result : Result (List Value) Value),
    evaluate state env expressions = (next, result) ∧
    isInsertOracle ci f state.evalState ∧ result ≠ .err (.abort .typeError) →
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env expressions =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)

/-- Module case of the original evaluator induction, using the induction
hypothesis for its contained declarations. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Dmod {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (name : ModN) (ds : List Dec)
    (ih : DecsOracleAdjustedAt compile ci f state env ds) :
    DecsOracleAdjustedAt compile ci f state env [.dmod name ds] := by
  intro next result ⟨source, inserted, safe⟩
  cases run : evaluateDecs state env ds with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [evaluateDecs, run] using source
      have innerSafe : (Result.err error : Result (SemEnv Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := ih middle (.err error) ⟨run, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [evaluateDecs, replacement]⟩
    | val innerEnv =>
      have pair : (middle, .val { v := Flapjack.NamespaceHOL.nsLift name innerEnv.v,
                                  c := Flapjack.NamespaceHOL.nsLift name innerEnv.c }) = (next, result) := by
        simpa [evaluateDecs, run] using source
      obtain ⟨middleInserted, replacement⟩ := ih middle (.val innerEnv) ⟨run, inserted, (by simp)⟩
      cases pair
      exact ⟨middleInserted, by simp [evaluateDecs, replacement]⟩

/-- Local-declaration case, with induction hypotheses for the private and
visible declarations. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Dlocal {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (locals body : List Dec)
    (ih : (∀ (middle : State F) (outcome : Result (SemEnv Value) Value) (innerEnv : SemEnv Value),
      evaluateDecs state env locals = (middle, outcome) ∧ outcome = .val innerEnv →
        DecsOracleAdjustedAt compile ci f middle (extendDecEnv innerEnv env) body) ∧
      DecsOracleAdjustedAt compile ci f state env locals) :
    DecsOracleAdjustedAt compile ci f state env [.dlocal locals body] := by
  obtain ⟨bodyIH, localsIH⟩ := ih
  intro next result ⟨source, inserted, safe⟩
  rw [evaluateDecs_local] at source ⊢
  cases run : evaluateDecs state env locals with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [run] using source
      have innerSafe : (Result.err error : Result (SemEnv Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := localsIH middle (.err error) ⟨run, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [replacement]⟩
    | val innerEnv =>
      have bodyRun : evaluateDecs middle (extendDecEnv innerEnv env) body = (next, result) := by
        simpa [run] using source
      obtain ⟨middleInserted, replacement⟩ := localsIH middle (.val innerEnv) ⟨run, inserted, (by simp)⟩
      obtain ⟨nextInserted, bodyReplacement⟩ :=
        bodyIH middle (.val innerEnv) innerEnv ⟨run, rfl⟩ next result ⟨bodyRun, middleInserted, safe⟩
      exact ⟨nextInserted, by simpa [replacement] using bodyReplacement⟩

/-- Non-singleton declaration-list case of the evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_DecsCons {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (first second : Dec) (rest : List Dec)
    (ih : (∀ (middle : State F) (outcome : Result (SemEnv Value) Value) (innerEnv : SemEnv Value),
      evaluateDecs state env [first] = (middle, outcome) ∧ outcome = .val innerEnv →
        DecsOracleAdjustedAt compile ci f middle (extendDecEnv innerEnv env) (second :: rest)) ∧
      DecsOracleAdjustedAt compile ci f state env [first]) :
    DecsOracleAdjustedAt compile ci f state env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro next result ⟨source, inserted, safe⟩
  rw [evaluateDecs_cons] at source ⊢
  cases run : evaluateDecs state env [first] with
  | mk middle inner =>
    cases inner with
    | err error =>
      have pair : (middle, .err error) = (next, result) := by simpa [run] using source
      have innerSafe : (Result.err error : Result (SemEnv Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply safe
        have h := congrArg Prod.snd pair
        simpa [bad] using h.symm
      obtain ⟨middleInserted, replacement⟩ := firstIH middle (.err error) ⟨run, inserted, innerSafe⟩
      cases pair
      exact ⟨middleInserted, by simp [replacement]⟩
    | val innerEnv =>
      cases tailRun : evaluateDecs middle (extendDecEnv innerEnv env) (second :: rest) with
      | mk final tailResult =>
        have pair : (final, combineDecResult innerEnv tailResult) = (next, result) := by
          simpa [run, tailRun] using source
        have tailSafe : tailResult ≠ .err (.abort .typeError) := by
          intro bad
          apply safe
          have h := congrArg Prod.snd pair
          simpa [bad, combineDecResult] using h.symm
        obtain ⟨middleInserted, replacement⟩ := firstIH middle (.val innerEnv) ⟨run, inserted, (by simp)⟩
        obtain ⟨finalInserted, tailReplacement⟩ :=
          tailIH middle (.val innerEnv) innerEnv ⟨run, rfl⟩ final tailResult ⟨tailRun, middleInserted, tailSafe⟩
        cases pair
        exact ⟨finalInserted, by simp [replacement, tailReplacement]⟩

/-- Value-declaration case of the evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "adjust_oracle_evaluate"]
theorem adjustOracle_evaluate_Dlet {Config F : Type} (compile : List Dec → List Dec)
    (ci : CompilerInstance Config) (f : List Dec → List Dec)
    (_preserves : ∀ (s : State F) (env : SemEnv Value) (ds : List Dec) (next : State F)
      (res : Result (SemEnv Value) Value),
      evaluateDecs s env ds = (next, res) ∧ res ≠ .err (.abort .typeError) →
        evaluateDecs s env (compile ds) = (next, res))
    (state : State F) (env : SemEnv Value) (locs : Flapjack.Misc.Location.Locs) (pat : Pat) (expr : AstHOL.Exp)
    (ih : ((patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true) →
      ExpsOracleAdjustedAt compile ci f state env [expr]) :
    DecsOracleAdjustedAt compile ci f state env [.dlet locs pat expr] := by
  intro next result ⟨source, inserted, safe⟩
  classical
  by_cases check : (patBindings pat).Nodup ∧ everyExp (oneConCheck env.c) expr = true
  · cases run : evaluate state env [expr] with
    | mk middle inner =>
      cases inner with
      | err error =>
        have pair : (middle, .err error) = (next, result) := by simpa [evaluateDecs, check, run] using source
        have innerSafe : (Result.err error : Result (List Value) Value) ≠ .err (.abort .typeError) := by
          intro bad
          apply safe
          have h := congrArg Prod.snd pair
          have errorEq : error = .abort .typeError := Result.err.inj bad
          simpa [errorEq] using h.symm
        obtain ⟨middleInserted, replacement⟩ := ih check middle (.err error) ⟨run, inserted, innerSafe⟩
        cases pair
        exact ⟨middleInserted, by simp [evaluateDecs, check, replacement]⟩
      | val values =>
        obtain ⟨middleInserted, replacement⟩ := ih check middle (.val values) ⟨run, inserted, (by simp)⟩
        cases matched : pmatch env.c middle.refs pat (headValue values) [] with
        | typeError =>
          simp [evaluateDecs, check, run, matched, typeError] at source
          obtain ⟨_, rfl⟩ := source
          exact (safe rfl).elim
        | noMatch =>
          simp [evaluateDecs, check, run, matched] at source
          obtain ⟨rfl, rfl⟩ := source
          exact ⟨middleInserted, by simp [evaluateDecs, check, replacement, matched]⟩
        | «match» bindings =>
          simp [evaluateDecs, check, run, matched] at source
          obtain ⟨rfl, rfl⟩ := source
          exact ⟨middleInserted, by simp [evaluateDecs, check, replacement, matched]⟩
  · simp [evaluateDecs, check, typeError] at source
    obtain ⟨_, rfl⟩ := source
    exact (safe rfl).elim

end Flapjack.Compiler.Backend.SourceEval.Proofs
