import Flapjack.Compiler.Backend.FlatPattern.Proofs.ExpressionList

/-! Clock-bounded expression-list simulation for the flat pattern pass. The
underlying evaluator and relations remain pending HOL review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Expression simulation restricted to states at or below a clock bound. -/
def ExpressionSimulationUpTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (expression : FlatLang.Exp) : Prop :=
  ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
    (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
    source.clock ≤ clock → FlatSem.evaluate sourceEnv source [expression] = (sourceFinal, sourceResult) →
    EnvRel n sourceEnv targetEnv → StateRel stateCfg source target → (compileExp cfg expression).1 < n →
    sourceResult ≠ .err (.abort .typeError) →
    ∃ targetFinal targetResult,
      FlatSem.evaluate targetEnv target [(compileExp cfg expression).2.2] = (targetFinal, targetResult) ∧
      StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult

/-- Expression-list simulation restricted to the same clock bound. -/
def ExpressionsSimulationUpTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (expressions : List FlatLang.Exp) : Prop :=
  ∀ (sourceEnv targetEnv : FlatSem.Environment FlatSem.Value) (source target sourceFinal : FlatSem.State C F)
    (sourceResult : Result (List FlatSem.Value) FlatSem.Value) (n : Nat),
    source.clock ≤ clock → FlatSem.evaluate sourceEnv source expressions = (sourceFinal, sourceResult) →
    EnvRel n sourceEnv targetEnv → StateRel stateCfg source target → (compileExps cfg expressions).1 < n →
    sourceResult ≠ .err (.abort .typeError) →
    ∃ targetFinal targetResult,
      FlatSem.evaluate targetEnv target (compileExps cfg expressions).2.2 = (targetFinal, targetResult) ∧
      StateRel stateCfg sourceFinal targetFinal ∧ FlatResultRel sourceResult targetResult

/-- Compiling an expression list preserves evaluation when each member satisfies
the expression induction hypothesis. -/
theorem compileExps_simulation_upTo {C F : Type} (cfg stateCfg : Config) (clock : Nat) (expressions : List FlatLang.Exp)
    (membersIH : ∀ expression ∈ expressions, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression) :
    ExpressionsSimulationUpTo (C := C) (F := F) cfg stateCfg clock expressions := by
  induction expressions with
  | nil =>
    intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
    simp [FlatSem.evaluate] at sourceEval
    rcases sourceEval with ⟨rfl, rfl⟩
    exact ⟨target, .val [], by simp [compileExps, FlatSem.evaluate], states, .values .nil⟩
  | cons first rest ih =>
    have firstIH := membersIH first (by simp)
    have restIH : ∀ expression ∈ rest, ExpressionSimulationUpTo (C := C) (F := F) cfg stateCfg clock expression := by
      intro expression member
      exact membersIH expression (List.mem_cons_of_mem _ member)
    cases rest with
    | nil =>
      intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
      have firstBound : (compileExp cfg first).1 < n := by
        have bounds := compileExps_cons_bounds cfg first []
        omega
      obtain ⟨targetFinal, targetResult, targetRun, finalRel, resultRel⟩ :=
        firstIH sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states firstBound safe
      exact ⟨targetFinal, targetResult, by simpa [compileExps_rows] using targetRun, finalRel, resultRel⟩
    | cons second rest =>
      have tailSim := ih restIH
      intro sourceEnv targetEnv source target sourceFinal sourceResult n clockBound sourceEval envs states bound safe
      have bounds := compileExps_cons_bounds cfg first (second :: rest)
      have firstBound : (compileExp cfg first).1 < n := by omega
      have tailBound : (compileExps cfg (second :: rest)).1 < n := by omega
      cases firstRun : FlatSem.evaluate sourceEnv source [first] with
      | mk sourceNext firstResult =>
        have firstSafe : firstResult ≠ .err (.abort .typeError) := by
          intro bad
          subst firstResult
          have outer := evaluate_list_first_error sourceEnv source sourceNext first second rest (.abort .typeError) firstRun
          rw [sourceEval] at outer
          exact safe (congrArg Prod.snd outer)
        obtain ⟨targetNext, targetFirstResult, targetFirstRun, nextStates, firstRelated⟩ := firstIH
          sourceEnv targetEnv source target sourceNext firstResult n clockBound firstRun envs states firstBound firstSafe
        cases firstRelated with
        | error errorsRel =>
          rename_i leftError rightError
          have sourceOuter := evaluate_list_first_error sourceEnv source sourceNext first second rest leftError firstRun
          have targetOuter := evaluate_list_first_error targetEnv target targetNext (compileExp cfg first).2.2
            ((compileExp cfg second).2.2) (rest.map (fun expression => (compileExp cfg expression).2.2)) rightError targetFirstRun
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          exact ⟨_, _, by simpa [compileExps_rows] using targetOuter,
            stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
        | values valuesRel =>
          rename_i sourceValues targetValues
          obtain ⟨value, valueEq⟩ := singletonSuccess first sourceEnv source sourceNext sourceValues firstRun
          subst sourceValues
          cases valuesRel with
          | cons valueRel tailRel =>
            cases tailRel
            rename_i value'
            let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
            let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
            have fixedStates := stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
            cases tailRun : FlatSem.evaluate sourceEnv sourceFixed (second :: rest) with
            | mk sourceLast tailResult =>
              have tailSafe : tailResult ≠ .err (.abort .typeError) := by
                intro bad
                subst tailResult
                have outer := evaluate_list_tail_error sourceEnv source sourceNext sourceLast first second rest value
                  (.abort .typeError) firstRun tailRun
                rw [sourceEval] at outer
                exact safe (congrArg Prod.snd outer)
              obtain ⟨targetLast, targetTailResult, targetTailRun, finalRel, tailRelated⟩ := tailSim
                sourceEnv targetEnv sourceFixed targetFixed sourceLast tailResult n (by dsimp [sourceFixed]; omega) tailRun envs fixedStates tailBound tailSafe
              cases tailRelated with
              | error errorsRel =>
                rename_i leftError rightError
                have sourceOuter := evaluate_list_tail_error sourceEnv source sourceNext sourceLast first second rest value
                  leftError firstRun tailRun
                have targetOuter := evaluate_list_tail_error targetEnv target targetNext targetLast (compileExp cfg first).2.2
                  ((compileExp cfg second).2.2) (rest.map (fun expression => (compileExp cfg expression).2.2)) value'
                  rightError targetFirstRun (by simpa [compileExps_rows] using targetTailRun)
                have equal := sourceEval.symm.trans sourceOuter
                cases equal
                exact ⟨targetLast, _, by simpa [compileExps_rows] using targetOuter, finalRel, .error errorsRel⟩
              | values tailValuesRel =>
                rename_i sourceTailValues targetTailValues
                have sourceOuter := evaluate_list_values sourceEnv source sourceNext sourceLast first second rest value
                  sourceTailValues firstRun tailRun
                have targetOuter := evaluate_list_values targetEnv target targetNext targetLast (compileExp cfg first).2.2
                  ((compileExp cfg second).2.2) (rest.map (fun expression => (compileExp cfg expression).2.2)) value'
                  targetTailValues targetFirstRun (by simpa [compileExps_rows] using targetTailRun)
                have equal := sourceEval.symm.trans sourceOuter
                cases equal
                exact ⟨targetLast, _, by simpa [compileExps_rows] using targetOuter, finalRel,
                  .values (.cons valueRel tailValuesRel)⟩


end Flapjack.Compiler.Backend.FlatPattern
