import Flapjack.Compiler.Backend.BviTmc.Proofs.ClockHypothesis
import Flapjack.Compiler.Backend.BviTmc.Proofs.ThunkRelation

/-! Clocked thunk-forcing simulation for TMC. -/
namespace Flapjack.Compiler.Backend.BviTmc.ForceSimulation
open BviTmc BviSem BvlSem ListSimulation ClockHypothesis SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: a related result cannot be a return exception
when the source result cannot be one. -/
theorem related_no_return (f : HolFiniteMapExact Nat Nat) (source target : BviResult)
    (related : resultRel (List.Forall₂ (valueRel f)) (eorRel f) source target)
    (sourceNoReturn : ∀ values, source ≠ .err (.raise (.ret values))) :
    ∀ values, target ≠ .err (.raise (.ret values)) := by
  intro values eq
  subst target
  cases source with
  | val _ => simp [resultRel] at related
  | err error =>
    cases error with
    | abort _ => simp [resultRel, excRel] at related
    | raise payload =>
      cases payload with
      | exn _ => simp [resultRel, excRel, eorRel] at related
      | ret values' => exact sourceNoReturn values' rfl

/-- Flapjack infrastructure: ordinary simulation of thunk forcing, using
the smaller-clock singleton induction for an unevaluated thunk's body. -/
theorem evaluate_force_core {C F : Type} (location index : Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.force location index] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (states : stateRel f source target) (ih : SmallerClockIH (C := C) (F := F) source.clock) :
    Core [.force location index] env2 f target result final := by
  have bound : index < env1.length := by
    by_contra invalid
    have failure : evaluate [.force location index] env1 source = (.err (.abort .typeError), source) := by
      simp [BviSem.evaluate, invalid]
    rw [run] at failure
    exact notTypeError (congrArg Prod.fst failure)
  have targetBound : index < env2.length := by have len := envRel_length opt f env1 env2 environments; omega
  have sourceAt : env1[index]? = some (holEl index env1) := by
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨bound, (holEl_eq_getElem index env1 bound).symm⟩
  have targetAt : env2[index]? = some (holEl index env2) := by
    apply List.getElem?_eq_some_iff.mpr
    exact ⟨targetBound, (holEl_eq_getElem index env2 targetBound).symm⟩
  have thunkValues := envRel_el opt f env1 env2 index environments bound
  have thunkRelated := destThunk_rel opt f env1 env2 source target index environments states bound
  simp only [destThunkRetRel] at thunkRelated
  rcases thunkRelated with ⟨sourceBad, targetBad⟩ | ⟨sourceBad, targetBad⟩ |
    ⟨mode, targetMode, value, value', sourceThunk, targetThunk, rfl, valuesRelated⟩
  · simp [BviSem.evaluate, sourceAt, sourceBad] at run
    exact False.elim (notTypeError run.1.symm)
  · simp [BviSem.evaluate, sourceAt, sourceBad] at run
    exact False.elim (notTypeError run.1.symm)
  · cases mode with
    | evaluated =>
      simp [BviSem.evaluate, sourceAt, sourceThunk] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      refine ⟨target, f, .val [value'], ?_, .cons valuesRelated .nil, states, ?_,
        onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
      · simp [BviSem.evaluate, targetAt, targetThunk]
      · intro key val h; exact h
    | notEvaluated =>
      cases sourceFound : findCode (some location) [holEl index env1, value] source.code with
      | none =>
        simp [BviSem.evaluate, sourceAt, sourceThunk, sourceFound] at run
        exact False.elim (notTypeError run.1.symm)
      | some pair =>
        obtain ⟨args, body⟩ := pair
        have values : List.Forall₂ (valueRel f) [holEl index env1, value] [holEl index env2, value'] :=
          .cons thunkValues (.cons valuesRelated .nil)
        obtain ⟨safe, args', body', loc', targetFound, argsRel, _, changed⟩ :=
          findCode_rel f _ _ source target (some location) args body sourceFound values states
        by_cases zero : source.clock = 0
        · have targetZero : target.clock = 0 := by simpa [states.2.1] using zero
          simp [BviSem.evaluate, sourceAt, sourceThunk, sourceFound, zero] at run
          obtain ⟨rfl, rfl⟩ := run.symm
          refine ⟨{ target with clock := 0 }, f, .err (.abort .timeoutError), ?_, rfl,
            stateRel_with_clock 0 f source target states, ?_, onlyFresh_refl f target.refs,
            holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
          · simp [BviSem.evaluate, targetAt, targetThunk, targetFound, targetZero]
          · intro key val h; exact h
        · have targetNonzero : target.clock ≠ 0 := by simpa [states.2.1] using zero
          simp only [BviSem.evaluate, sourceAt, sourceThunk, sourceFound, zero, ↓reduceIte] at run
          cases bodyRun : evaluate [body] args (BviSem.decClock 1 source) with
          | mk bodyResult bodyFinal =>
            simp only [bodyRun] at run
            have bodyPair : (bodyResult, bodyFinal) = (result, final) := by
              cases bodyResult with
              | val values => simpa [bodyRun] using run
              | err error =>
                cases error with
                | abort reason => simpa [bodyRun] using run
                | raise payload =>
                  cases payload with
                  | exn value => simpa [bodyRun] using run
                  | ret values => simp at run; exact False.elim (notTypeError run.1.symm)
            have noReturn : ∀ values, bodyResult ≠ .err (.raise (.ret values)) := by
              intro values bad
              rw [bad] at run
              simp at run
              exact notTypeError run.1.symm
            cases bodyPair
            have smaller : (BviSem.decClock 1 source).clock < source.clock := by simp [BviSem.decClock]; omega
            have decStates : stateRel f (BviSem.decClock 1 source) (BviSem.decClock 1 target) := by
              simpa [BviSem.decClock, states.2.1] using stateRel_with_clock (source.clock - 1) f source target states
            have bodyPost := ih body (BviSem.decClock 1 source) (BviSem.decClock 1 target) args args' false f loc'
              result final smaller bodyRun safe argsRel decStates notTypeError
            have bodyCore : Core [body'] args' f (BviSem.decClock 1 target) result final := by
              by_cases same : body = body'
              · subst body'; exact bodyPost.1
              · obtain ⟨workerLoc, optimized, rewrite⟩ := changed same
                exact (bodyPost.2 workerLoc optimized).1 body' rewrite
            obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ := bodyCore
            have targetNoReturn := related_no_return g result targetResult related noReturn
            refine ⟨next, g, targetResult, ?_, related, nextStates, extension, fresh, unchanged, still⟩
            rw [BviSem.evaluate]
            simp only [targetAt, targetThunk, targetFound, targetNonzero, ↓reduceIte]
            rw [targetRun]
            cases targetResult with
            | val values => rfl
            | err error =>
              cases error with
              | abort reason => rfl
              | raise payload =>
                cases payload with
                | exn value => rfl
                | ret values => exact False.elim (targetNoReturn values rfl)

/-- Flapjack infrastructure: the full singleton force case, including the
optimized worker, from the smaller-clock singleton induction hypothesis. -/
theorem evaluate_force_from_clock {C F : Type} (loc location index : Nat)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.force location index] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (environments : envRel opt f env1 env2)
    (states : stateRel f source target) (ih : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.force location index) source target env1 env2 opt f loc result final := by
  have core := evaluate_force_core location index source target env1 env2 opt f result final run notTypeError
    environments states ih
  refine ⟨core, ?_⟩
  intro dest code
  constructor
  · intro wrapper rewrite
    simp [rewriteWrapperSource] at rewrite
  · intro optTrue ptr c hole notFinal pointer
    have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
    obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ := core
    obtain ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩ :=
      FillHole.evaluate_fill_hole (.force location index) f g env1 env2 source final target next result targetResult c ptr
        run targetRun optEnv states extension related hole notFinal unchanged still fresh nextStates pointer
    simpa only [rewriteWorkerSource] using
      (show IfWorker.WorkerCore (fillHoleSource env1.length (env1.length + 1) (.force location index))
        env1 env2 f target ptr result final from ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩)

end Flapjack.Compiler.Backend.BviTmc.ForceSimulation
