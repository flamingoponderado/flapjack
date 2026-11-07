import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateFull

/-! Singleton and declaration specializations of the flat evaluation
simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- Clear the only environment field, allowing its value type to change as in
HOL's polymorphic record update. This is Flapjack-specific infrastructure. -/
def emptyEnvironment {α β : Type} (_env : FlatSem.Environment α) : FlatSem.Environment β := ⟨[]⟩

/-- Singleton evaluation in an empty environment preserves the flat state
relation. The evaluator and carriers remain pending HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_sing_keep_flat_state_rel_eq"]
theorem evaluate_sing_keep_flatStateRel {C F α : Type} (env : FlatSem.Environment α)
    (state : FlatSem.State C F) (expressions : List FlatLang.Exp) (next : FlatSem.State C F)
    (result : Result (List FlatSem.Value) FlatSem.Value) (expression : FlatLang.Exp)
    (reachable : NumSet) (target : FlatSem.State C F)
    (run : FlatSem.evaluate (emptyEnvironment env) state expressions = (next, result))
    (related : flatStateRel reachable state target) (singleton : expressions = [expression])
    (_kept : keep reachable expression = true) (lookupsClosed : globalsWithin (findLookups expression) reachable)
    (expressionSafe : hasEval expression = false) (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, FlatSem.evaluate (emptyEnvironment env) target expressions = (targetNext, result) ∧
      flatStateRel reachable next targetNext := by
  subst expressions
  have envClosed : globalsWithin (findEnvGlobals (emptyEnvironment env)) reachable := by
    simp [emptyEnvironment, findEnvGlobals, findValuesGlobals, globalsWithin, sptMem, sptDomain]
  have envSafe : bindingsNoEval ([] : List (Flapjack.AstHOL.VarN × FlatSem.Value)) := by
    simp [bindingsNoEval]
  obtain ⟨targetNext, evaluated, nextRelated, _, _⟩ :=
    evaluate_keep_flatStateRel [expression] (emptyEnvironment env) state next result reachable target run
      (singletonLookups_within expression reachable lookupsClosed) related envClosed envSafe
      (singletonExpression_noEval expression expressionSafe) notTypeError
  exact ⟨targetNext, evaluated, nextRelated⟩

/-- A kept declaration in a closed singleton program only reads reachable
globals. This is a Flapjack helper for the declaration simulation. -/
theorem kept_declaration_lookups_closed (reachable : NumSet) (expression : FlatLang.Exp)
    (closed : decsClosed reachable [expression]) (kept : keep reachable expression = true) :
    globalsWithin (findLookups expression) reachable := by
  have analysis : analyseCode [expression] = analyseExp expression := by
    cases expAnalysis : analyseExp expression with
    | mk roots tree =>
      have unionEmpty : sptUnion roots .ln = roots := by cases roots <;> simp [sptUnion]
      have treeEmpty : numSetTreeUnion tree .ln = tree := by cases tree <;> rfl
      simp [analyseCode, codeAnalysisUnion, expAnalysis, unionEmpty, treeEmpty]
  cases pure : isPure expression with
  | false =>
    have analysis' : analyseCode [expression] =
        (sptUnion (findLoc expression) (findLookups expression),
         sptMap (fun _ => .ln) (sptUnion (findLoc expression) (findLookups expression))) := by
      simpa [analyseExp, pure] using analysis
    have roots := (closed _ _ analysis').1
    intro key member
    exact roots key ((sptMem_sptUnion _ _ _).mpr (Or.inr member))
  | true =>
    have nonempty : sptIsEmpty (sptInter (findLoc expression) reachable) = false := by
      cases empty : sptIsEmpty (sptInter (findLoc expression) reachable) <;> simp [keep, pure, empty] at kept ⊢
    obtain ⟨source, stored, found⟩ := sptWf_exists_key _ (sptWfInter _ _) nonempty
    rw [sptLookup_sptInterCases] at found
    cases locFound : sptLookup source (findLoc expression) <;> simp [locFound] at found
    case some loc =>
      cases reachFound : sptLookup source reachable <;> simp [reachFound] at found
      case some reach =>
        have sourceReachable : sptMem source reachable := by simp [sptMem, sptDomain, reachFound]
        have sourceLoc : sptLookup source (findLoc expression) = some () := by
          cases loc
          exact locFound
        have analysis' : analyseCode [expression] =
            ((if isHidden expression then .ln else findLoc expression),
              sptMap (fun _ => findLookups expression) (findLoc expression)) := by
          simpa [analyseExp, pure] using analysis
        have paths := (closed _ _ analysis').2
        intro key member
        apply paths source key sourceReachable
        apply Relation.ReflTransGen.single
        refine ⟨findLookups expression, ?_, ?_⟩
        · simp [sptLookup_sptMap, sourceLoc]
        · cases foundKey : sptLookup key (findLookups expression) with
          | none => simp [sptMem, sptDomain, foundKey] at member
          | some value => cases value; rfl

/-- Evaluation of a kept declaration preserves the flat state relation. The
evaluator and carriers remain pending HOL correspondence review. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "evaluate_dec_flat_state_rel"]
theorem evaluate_dec_flatStateRel {C F : Type} (state : FlatSem.State C F) (declaration : FlatLang.Exp)
    (next : FlatSem.State C F) (result : Option (ErrorResult FlatSem.Value))
    (reachable : NumSet) (target : FlatSem.State C F)
    (run : FlatSem.evaluateDec state declaration = (next, result))
    (closed : decsClosed reachable [declaration]) (related : flatStateRel reachable state target)
    (kept : keep reachable declaration = true) (safe : hasEvalDec declaration = false)
    (notTypeError : result ≠ some (.abort .typeError)) :
    ∃ targetNext, FlatSem.evaluateDec target declaration = (targetNext, result) ∧
      flatStateRel reachable next targetNext := by
  cases evaluated : FlatSem.evaluate ⟨[]⟩ state [declaration] with
  | mk bodyState bodyResult =>
    have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      simp [FlatSem.evaluateDec, evaluated] at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetNext, targetEval, nextRelated⟩ :=
      evaluate_sing_keep_flatStateRel (⟨[]⟩ : FlatSem.Environment FlatSem.Value) state [declaration] bodyState bodyResult declaration reachable target
        evaluated related rfl kept (kept_declaration_lookups_closed reachable declaration closed kept)
        (by simpa [hasEvalDec] using safe) bodyNotTypeError
    dsimp [emptyEnvironment] at targetEval
    refine ⟨targetNext, ?_, ?_⟩
    · cases bodyResult with
      | err error =>
        simp [FlatSem.evaluateDec, evaluated] at run
        rcases run with ⟨_, rfl⟩
        simp [FlatSem.evaluateDec, targetEval]
      | val values =>
        simp only [FlatSem.evaluateDec, evaluated] at run
        simp only [FlatSem.evaluateDec, targetEval]
        split at run <;> simp_all
    · cases bodyResult with
      | err error =>
        simp [FlatSem.evaluateDec, evaluated] at run
        rcases run with ⟨rfl, _⟩
        exact nextRelated
      | val values =>
        simp only [FlatSem.evaluateDec, evaluated] at run
        split at run <;> simp_all

end Flapjack.Compiler.Backend.FlatElim
