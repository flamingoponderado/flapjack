import Flapjack.Compiler.Backend.FlatPattern.Proofs.DeclarationEvaluation
import Flapjack.Compiler.Backend.FlatPattern.Proofs.ClockedExpressionCases

/-! Clock-bounded declaration simulation for flat pattern compilation. The
evaluator and proof-side relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Compiled declaration evaluation preserves successful and non-type-error
outcomes when the declaration expression satisfies its induction hypothesis. -/
theorem evaluateDec_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (declaration : FlatLang.Exp)
    (expressionIH : ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock declaration)
    (source target sourceFinal : FlatSem.State C F) (outcome : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value))
    (clockBound : source.clock ≤ clock) (states : StateRel stateCfg source target)
    (run : FlatSem.evaluateDec source declaration = (sourceFinal, outcome))
    (safe : outcome ≠ some (.abort .typeError)) :
    ∃ targetFinal targetOutcome,
      FlatSem.evaluateDec target (compileDec cfg declaration) = (targetFinal, targetOutcome) ∧
      StateRel stateCfg sourceFinal targetFinal ∧ optionRel FlatErrorRel outcome targetOutcome := by
  classical
  cases expressionRun : FlatSem.evaluate ⟨[]⟩ source [declaration] with
  | mk sourceNext expressionResult =>
    have expressionSafe : expressionResult ≠ .err (.abort .typeError) := by
      intro bad
      subst expressionResult
      simp [FlatSem.evaluateDec, expressionRun] at run
      exact safe run.2.symm
    let n := (compileExp cfg declaration).1 + 1
    obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := expressionIH
      ⟨[]⟩ ⟨[]⟩ source target sourceNext expressionResult n clockBound expressionRun (envRel_empty n) states (by dsimp [n]; omega) expressionSafe
    cases related with
    | error errorsRel =>
      rename_i sourceError targetError
      have sourceShape : sourceNext = sourceFinal ∧ some sourceError = outcome := by
        simpa [FlatSem.evaluateDec, expressionRun] using run
      rcases sourceShape with ⟨rfl, rfl⟩
      refine ⟨targetNext, some targetError, ?_, nextStates, ?_⟩
      · unfold FlatSem.evaluateDec compileDec
        rw [targetRun]
      · exact errorsRel
    | values valuesRel =>
      rename_i sourceValues targetValues
      have sourceShape : sourceNext = sourceFinal ∧
          (if sourceValues = [FlatSem.unitValue] then none else some (.abort .typeError)) = outcome := by
        cases sourceValues with
        | nil => simpa [FlatSem.evaluateDec, expressionRun] using run
        | cons first rest =>
          cases rest with
          | cons _ _ => simpa [FlatSem.evaluateDec, expressionRun] using run
          | nil =>
            cases first <;> simp_all [FlatSem.evaluateDec, FlatSem.unitValue]
            all_goals split at run <;> simp_all
      obtain ⟨rfl, sourceOutcome⟩ := sourceShape
      by_cases isUnit : sourceValues = [FlatSem.unitValue]
      · subst sourceValues
        simp at sourceOutcome
        subst outcome
        cases valuesRel with
        | cons unitRel tailRel =>
          cases tailRel
          rename_i targetValue
          have unitEq := valueRel_unit targetValue unitRel
          subst targetValue
          refine ⟨targetNext, none, ?_, nextStates, ?_⟩
          · unfold FlatSem.evaluateDec compileDec
            rw [targetRun]
            rfl
          · trivial
      · simp [isUnit] at sourceOutcome
        exact (safe sourceOutcome.symm).elim

/-- A list of declarations preserves related states and optional errors when
each declaration has the expression simulation induction hypothesis. -/
theorem evaluateDecs_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (declarations : List FlatLang.Exp)
    (membersIH : ∀ declaration ∈ declarations, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock declaration)
    (source target sourceFinal : FlatSem.State C F) (outcome : Option (SemanticPrimitivesHOL.ErrorResult FlatSem.Value))
    (clockBound : source.clock ≤ clock) (states : StateRel stateCfg source target) (run : FlatSem.evaluateDecs source declarations = (sourceFinal, outcome))
    (safe : outcome ≠ some (.abort .typeError)) :
    ∃ targetFinal targetOutcome,
      FlatSem.evaluateDecs target (declarations.map (compileDec cfg)) = (targetFinal, targetOutcome) ∧
      StateRel stateCfg sourceFinal targetFinal ∧ optionRel FlatErrorRel outcome targetOutcome := by
  induction declarations generalizing source target sourceFinal outcome with
  | nil =>
    simp [FlatSem.evaluateDecs] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, none, by simp [FlatSem.evaluateDecs], states, trivial⟩
  | cons declaration rest ih =>
    have firstIH := membersIH declaration (by simp)
    have restIH : ∀ declaration ∈ rest, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock declaration := by
      intro item member
      exact membersIH item (List.mem_cons_of_mem _ member)
    cases firstRun : FlatSem.evaluateDec source declaration with
    | mk sourceNext firstOutcome =>
      cases firstOutcome with
      | some error =>
        have sourceShape : (sourceNext, some error) = (sourceFinal, outcome) := by
          simpa [FlatSem.evaluateDecs_cons, firstRun] using run
        cases sourceShape
        obtain ⟨targetNext, targetOutcome, targetFirst, nextStates, errorsRel⟩ :=
          evaluateDec_simulation_upTo cfg stateCfg clock declaration firstIH source target sourceFinal (some error) clockBound states firstRun safe
        cases targetOutcome with
        | none => simp [optionRel] at errorsRel
        | some targetError =>
          refine ⟨targetNext, some targetError, ?_, nextStates, errorsRel⟩
          simp [FlatSem.evaluateDecs_cons, targetFirst]
      | none =>
        have tailRun : FlatSem.evaluateDecs sourceNext rest = (sourceFinal, outcome) := by
          simpa [FlatSem.evaluateDecs_cons, firstRun] using run
        obtain ⟨targetNext, targetOutcome, targetFirst, nextStates, firstRel⟩ :=
          evaluateDec_simulation_upTo cfg stateCfg clock declaration firstIH source target sourceNext none clockBound states firstRun (by simp)
        cases targetOutcome with
        | some error => simp [optionRel] at firstRel
        | none =>
          obtain ⟨targetFinal, output, tailTarget, finalRel, outcomeRel⟩ :=
            ih restIH sourceNext targetNext sourceFinal outcome (by have h := FlatSem.evaluateDec_clock source declaration; rw [firstRun] at h; simp only at h; omega) nextStates tailRun safe
          refine ⟨targetFinal, output, ?_, finalRel, outcomeRel⟩
          simpa [FlatSem.evaluateDecs_cons, targetFirst] using tailTarget

end Flapjack.Compiler.Backend.FlatPattern
