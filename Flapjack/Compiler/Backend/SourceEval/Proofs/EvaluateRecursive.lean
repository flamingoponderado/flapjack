import Flapjack.Compiler.Backend.SourceEval.Proofs.EvaluateDeclarations
import Flapjack.EvaluateProps.Declarations

/-! Recursive declaration cases of source evaluator oracle adjustment. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.EvaluateProps

/-- The declaration induction hypothesis at a fixed declaration list. This is
Flapjack proof infrastructure, not a separate HOL declaration. -/
def DecsOracleAdjusted {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (program : List Dec) : Prop :=
  ∀ (state next : State F) (env : SemEnv Value) (result : Result (SemEnv Value) Value),
    evaluateDecs state env program = (next, result) →
    isInsertOracle ci f state.evalState → result ≠ .err (.abort .typeError) →
    isInsertOracle ci f next.evalState ∧
    evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env program =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)

/-- Expression induction hypothesis at a fixed list of expressions. This is
Flapjack proof infrastructure, not a separate HOL declaration. -/
def ExpsOracleAdjusted {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (expressions : List AstHOL.Exp) : Prop :=
  ∀ (state next : State F) (env : SemEnv Value) (result : Result (List Value) Value),
    evaluate state env expressions = (next, result) →
    isInsertOracle ci f state.evalState → result ≠ .err (.abort .typeError) →
    isInsertOracle ci f next.evalState ∧
    evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env expressions =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)

/-- Expression adjustment at a fixed input state and environment. This
Flapjack predicate represents the hypothesis for one recursive evaluation. -/
def ExpsOracleAdjustedAt {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (state : State F) (env : SemEnv Value)
    (expressions : List AstHOL.Exp) : Prop :=
  ∀ (next : State F) (result : Result (List Value) Value),
    evaluate state env expressions = (next, result) →
    isInsertOracle ci f state.evalState → result ≠ .err (.abort .typeError) →
    isInsertOracle ci f next.evalState ∧
      evaluate { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env expressions =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)

/-- Module case of the original evaluator induction, using the induction
hypothesis for its contained declarations. The recursive hypothesis here is stronger than the original fixed-state or conditionally selected induction hypothesis; this is Flapjack infrastructure and the faithful HOL case remains open. -/
theorem adjustOracle_evaluate_Dmod {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (name : ModN) (ds : List Dec) (ih : DecsOracleAdjusted (F := F) ci f compile ds)
    (state next : State F) (env : SemEnv Value) (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env [.dmod name ds] = (next, result))
    (inserted : isInsertOracle ci f state.evalState)
    (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.dmod name ds] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
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
      obtain ⟨middleInserted, replacement⟩ := ih state middle env (.err error) run inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [evaluateDecs, replacement]⟩
    | val innerEnv =>
      have pair : (middle, .val { v := Flapjack.NamespaceHOL.nsLift name innerEnv.v,
                                  c := Flapjack.NamespaceHOL.nsLift name innerEnv.c }) = (next, result) := by
        simpa [evaluateDecs, run] using source
      obtain ⟨middleInserted, replacement⟩ := ih state middle env (.val innerEnv) run inserted (by simp)
      cases pair
      exact ⟨middleInserted, by simp [evaluateDecs, replacement]⟩

/-- Local-declaration case, with induction hypotheses for the private and
visible declarations. The recursive hypothesis here is stronger than the original fixed-state or conditionally selected induction hypothesis; this is Flapjack infrastructure and the faithful HOL case remains open. -/
theorem adjustOracle_evaluate_Dlocal {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (locals body : List Dec) (localsIH : DecsOracleAdjusted (F := F) ci f compile locals)
    (bodyIH : DecsOracleAdjusted (F := F) ci f compile body)
    (state next : State F) (env : SemEnv Value) (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env [.dlocal locals body] = (next, result))
    (inserted : isInsertOracle ci f state.evalState)
    (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.dlocal locals body] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
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
      obtain ⟨middleInserted, replacement⟩ := localsIH state middle env (.err error) run inserted innerSafe
      cases pair
      exact ⟨middleInserted, by simp [replacement]⟩
    | val innerEnv =>
      have bodyRun : evaluateDecs middle (extendDecEnv innerEnv env) body = (next, result) := by
        simpa [run] using source
      obtain ⟨middleInserted, replacement⟩ := localsIH state middle env (.val innerEnv) run inserted (by simp)
      obtain ⟨nextInserted, bodyReplacement⟩ :=
        bodyIH middle next (extendDecEnv innerEnv env) result bodyRun middleInserted safe
      exact ⟨nextInserted, by simpa [replacement] using bodyReplacement⟩

/-- Non-singleton declaration-list case of the evaluator induction. The recursive hypothesis here is stronger than the original fixed-state or conditionally selected induction hypothesis; this is Flapjack infrastructure and the faithful HOL case remains open. -/
theorem adjustOracle_evaluate_DecsCons {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (first second : Dec) (rest : List Dec)
    (firstIH : DecsOracleAdjusted (F := F) ci f compile [first])
    (tailIH : DecsOracleAdjusted (F := F) ci f compile (second :: rest))
    (state next : State F) (env : SemEnv Value) (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env (first :: second :: rest) = (next, result))
    (inserted : isInsertOracle ci f state.evalState)
    (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env (first :: second :: rest) =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
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
      obtain ⟨middleInserted, replacement⟩ := firstIH state middle env (.err error) run inserted innerSafe
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
        obtain ⟨middleInserted, replacement⟩ := firstIH state middle env (.val innerEnv) run inserted (by simp)
        obtain ⟨finalInserted, tailReplacement⟩ :=
          tailIH middle final (extendDecEnv innerEnv env) tailResult tailRun middleInserted tailSafe
        cases pair
        exact ⟨finalInserted, by simp [replacement, tailReplacement]⟩

/-- Value-declaration case of the evaluator induction. The recursive hypothesis here is stronger than the original fixed-state or conditionally selected induction hypothesis; this is Flapjack infrastructure and the faithful HOL case remains open. -/
theorem adjustOracle_evaluate_Dlet {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (_compilePreserve : DeclarationCompilerPreserves (F := F) compile)
    (locs : Flapjack.Misc.Location.Locs) (pat : Pat) (expr : AstHOL.Exp)
    (ih : ExpsOracleAdjusted (F := F) ci f compile [expr])
    (state next : State F) (env : SemEnv Value) (result : Result (SemEnv Value) Value)
    (source : evaluateDecs state env [.dlet locs pat expr] = (next, result))
    (inserted : isInsertOracle ci f state.evalState)
    (safe : result ≠ .err (.abort .typeError)) :
    isInsertOracle ci f next.evalState ∧
      evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env [.dlet locs pat expr] =
        ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result) := by
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
        obtain ⟨middleInserted, replacement⟩ := ih state middle env (.err error) run inserted innerSafe
        cases pair
        exact ⟨middleInserted, by simp [evaluateDecs, check, replacement]⟩
      | val values =>
        obtain ⟨middleInserted, replacement⟩ := ih state middle env (.val values) run inserted (by simp)
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
