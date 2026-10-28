import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateControl

/-! Clock induction step for function application in the flat evaluation
simulation. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- The evaluation simulation at one fixed source environment and state.
This Flapjack-specific predicate exposes the clock induction hypothesis. -/
def evaluationSimulationAt {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (expressions : List FlatLang.Exp) : Prop :=
  ∀ (next : FlatSem.State C F) (result : Result (List FlatSem.Value) FlatSem.Value)
    (reachable : NumSet) (target : FlatSem.State C F),
    FlatSem.evaluate env source expressions = (next, result) →
    globalsWithin (findGlobalsList destGlobalVarLookup expressions) reachable →
    flatStateRel reachable source target → globalsWithin (findEnvGlobals env) reachable →
    bindingsNoEval env.v → expressionsNoEval expressions → result ≠ .err (.abort .typeError) →
    ∃ targetNext, FlatSem.evaluate env target expressions = (targetNext, result) ∧
      flatStateRel reachable next targetNext ∧ globalsWithin (findPrimitiveResultGlobals result) reachable ∧
      valuesNoEval (Flapjack.Compiler.Backend.FlatProps.resultValues result)

/-- Decrementing the clock of both states preserves their relation. -/
theorem flatStateRel_decClock {C F : Type} (reachable : NumSet) (source target : FlatSem.State C F)
    (related : flatStateRel reachable source target) :
    flatStateRel reachable (FlatSem.decClock source) (FlatSem.decClock target) := by
  obtain ⟨clock, refs, ffi, globals, refsClosed, refsSafe⟩ := related
  exact ⟨by simp [FlatSem.decClock, clock], refs, ffi, globals, refsClosed, refsSafe⟩

/-- Function application simulation at a fixed initial state, given the
argument-list induction hypothesis and simulation at all smaller clocks.
This is a clock-induction step, not the assembled HOL theorem. -/
theorem evaluate_call_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsIH : evaluationSimulation (C := C) (F := F) args.reverse)
    (smallerClock : ∀ (newEnv : FlatSem.Environment FlatSem.Value) (newState : FlatSem.State C F)
      (body : FlatLang.Exp), newState.clock < source.clock → evaluationSimulationAt newEnv newState [body]) :
    evaluationSimulationAt env source [.app tra (.src .opapp) args] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have argsClosed : globalsWithin (findGlobalsList destGlobalVarLookup args.reverse) reachable := by
    apply findLookupsList_reverse_within args reachable
    have appClosed := (findLookupsList_within_iff _ _).mp lookupsClosed (.app tra (.src .opapp) args) (by simp)
    exact (findLookups_app_within tra (.src .opapp) args reachable appClosed).1
  have argsSafe : expressionsNoEval args.reverse := by
    apply expressionsNoEval_reverse args
    apply (hasEvalList_eq_false_iff args).mp
    have safe := expressionsSafe (.app tra (.src .opapp) args) (by simp)
    simpa [hasEval] using safe
  cases argEval : FlatSem.evaluate env source args.reverse with
  | mk argState argResult =>
    simp only [FlatSem.evaluate, argEval, FlatSem.fixClock] at run
    have argNotTypeError : argResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetArgState, targetArgEval, argRelated, argClosed, argSafe⟩ :=
      argsIH env source argState argResult reachable target argEval argsClosed related envClosed envSafe argsSafe argNotTypeError
    have clampedRelated := flatStateRel_fixClock reachable source target argState targetArgState argResult related argRelated
    simp only [FlatSem.fixClock] at clampedRelated
    cases argResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ targetArgState with clock := min target.clock targetArgState.clock }, ?_, clampedRelated, argClosed, argSafe⟩
      simp [FlatSem.evaluate, targetArgEval, FlatSem.fixClock]
    | val values =>
      simp only at run
      have valuesClosed : globalsWithin (findValuesGlobals values.reverse) reachable := by
        apply findValuesGlobals_reverse_within
        simpa [findPrimitiveResultGlobals] using argClosed
      have valuesSafe : valuesNoEval values.reverse := by
        apply valuesNoEval_reverse
        simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using argSafe
      cases call : FlatSem.doOpApp values.reverse with
      | none =>
        simp [call] at run
        rcases run with ⟨_, rfl⟩
        exact (notTypeError rfl).elim
      | some pair =>
        obtain ⟨newEnv, body⟩ := pair
        have invariants := doOpApp_invariants values.reverse newEnv body reachable call valuesClosed valuesSafe
        have clockEq := clampedRelated.1
        by_cases zero : min source.clock argState.clock = 0
        · simp [call, zero] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ targetArgState with clock := min target.clock targetArgState.clock }, ?_, ?_, ?_, ?_⟩
          · simp [FlatSem.evaluate, targetArgEval, FlatSem.fixClock, call, ← clockEq, zero]
          · simpa [zero] using clampedRelated
          · simp [findPrimitiveResultGlobals, findResultGlobals, globalsWithin, sptMem, sptDomain]
          · simp [Flapjack.Compiler.Backend.FlatProps.resultValues, valuesNoEval]
        · simp [call, zero] at run
          have decrease : (FlatSem.decClock { argState with clock := min source.clock argState.clock }).clock < source.clock := by
            simp only [FlatSem.decClock]
            have bound := Nat.min_le_left source.clock argState.clock
            omega
          have recursiveRelated := flatStateRel_decClock reachable _ _ clampedRelated
          obtain ⟨targetNext, evaluated, nextRelated, closed, safe⟩ :=
            smallerClock newEnv _ body decrease next result reachable _ run
              (singletonLookups_within body reachable invariants.1) recursiveRelated invariants.2.2.1
              invariants.2.2.2 (singletonExpression_noEval body invariants.2.1) notTypeError
          refine ⟨targetNext, ?_, nextRelated, closed, safe⟩
          simpa [FlatSem.evaluate, targetArgEval, FlatSem.fixClock, call, ← clockEq, zero] using evaluated

end Flapjack.Compiler.Backend.FlatElim
