import Flapjack.Compiler.Backend.BviTmc.Proofs.StructuralHypothesis
import Flapjack.Compiler.Backend.BviTmc.Proofs.ForceSimulation

/-! Ordinary clocked calls in the TMC simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallSimulation
open BviTmc BviSem BvlSem ListSimulation ClockHypothesis StructuralHypothesis SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: ordinary simulation of a call without an
exception handler, using the smaller-weight argument induction and the
smaller-clock function-body induction. -/
theorem evaluate_call_no_handler_core {C F : Type} (loc ticks : Nat) (dest : Option Nat) (args : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.call ticks dest args none] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.call ticks dest args none))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.call ticks dest args none]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    Core [.call ticks dest args none] env2 f target result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have argsSafe : ∀ e ∈ args, noMutcons e := fun e member => safe.1 ⟨e, member⟩
  have argsWeight : expsWeight args < expsWeight [.call ticks dest args none] := by
    simp [BviSem.expsWeight, BviSem.expWeight]
    omega
  cases argsRun : evaluate args env1 source with
  | mk argsResult middle =>
    have argsNotError : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨middleTarget, g, targetArgsResult, targetArgsRun, argsRelated, middleStates,
      extension, fresh, unchanged, still⟩ :=
      (weightIH args source target env1 env2 false f loc argsResult middle (Nat.le_refl _) argsWeight
        argsRun argsSafe (envRel_relax opt f env1 env2 environments) states (by simp) argsNotError).1
    cases argsResult with
    | err error =>
      cases targetArgsResult with
      | val values => simp [resultRel] at argsRelated
      | err error' =>
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
        simp at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨middleTarget, g, .err error', ?_, argsRelated, middleStates, extension, fresh, unchanged, still⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgsRun]
        simp
    | val values =>
      cases targetArgsResult with
      | err error => simp [resultRel] at argsRelated
      | val values' =>
        cases found : findCode dest values middle.code with
        | none =>
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
          simp [found] at run
          exact False.elim (notTypeError run.1.symm)
        | some pair =>
          obtain ⟨callArgs, body⟩ := pair
          obtain ⟨bodySafe, callArgs', body', bodyLoc, targetFound, callEnv, _, changed⟩ :=
            findCode_rel g values values' middle middleTarget dest callArgs body found argsRelated middleStates
          by_cases timeout : middle.clock < ticks + 1
          · have targetTimeout : middleTarget.clock < ticks + 1 := by simpa [middleStates.2.1] using timeout
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
            simp [found, timeout] at run
            obtain ⟨rfl, rfl⟩ := run.symm
            refine ⟨{ middleTarget with clock := 0 }, g, .err (.abort .timeoutError), ?_, rfl,
              stateRel_with_clock 0 g middle middleTarget middleStates, extension, fresh, unchanged, still⟩
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgsRun]
            simp [targetFound, targetTimeout]
          · have targetEnough : ¬middleTarget.clock < ticks + 1 := by simpa [middleStates.2.1] using timeout
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
            simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
              found, timeout] at run
            rw [BviSem.fixClock_evaluate] at run
            cases bodyRun : evaluate [body] callArgs (BviSem.decClock (ticks + 1) middle) with
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
              have noReturn : ∀ vals, bodyResult ≠ .err (.raise (.ret vals)) := by
                intro vals bad
                rw [bad] at run
                simp at run
                exact notTypeError run.1.symm
              cases bodyPair
              have argsClock := BviSem.evaluate_clock_le args env1 source
              rw [argsRun] at argsClock
              dsimp only at argsClock
              have smaller : (BviSem.decClock (ticks + 1) middle).clock < source.clock := by
                simp [BviSem.decClock]
                omega
              have decStates : stateRel g (BviSem.decClock (ticks + 1) middle)
                  (BviSem.decClock (ticks + 1) middleTarget) := by
                simpa [BviSem.decClock, middleStates.2.1] using
                  stateRel_with_clock (middle.clock - (ticks + 1)) g middle middleTarget middleStates
              have post := clockIH body (BviSem.decClock (ticks + 1) middle) (BviSem.decClock (ticks + 1) middleTarget)
                callArgs callArgs' false g bodyLoc result final smaller bodyRun bodySafe callEnv decStates notTypeError
              have bodyCore : Core [body'] callArgs' g (BviSem.decClock (ticks + 1) middleTarget) result final := by
                by_cases same : body = body'
                · subst body'; exact post.1
                · obtain ⟨workerLoc, optimized, rewrite⟩ := changed same
                  exact (post.2 workerLoc optimized).1 body' rewrite
              obtain ⟨next, h, targetResult, targetBodyRun, related, nextStates, bodyExtension,
                bodyFresh, bodyUnchanged, bodyStill⟩ := bodyCore
              have targetNoReturn := ForceSimulation.related_no_return h result targetResult related noReturn
              have domain := BviProps.evaluate_refs_subset args env2 target middleTarget (.val values') targetArgsRun
              have totalExtension : finiteSubmap f h := fun key value found => bodyExtension key value (extension key value found)
              have totalFresh := onlyFresh_trans f g h target.refs middleTarget.refs fresh bodyFresh domain
              have totalUnchanged := holesUnchanged_trans f g target.refs middleTarget.refs next.refs ∅
                unchanged bodyUnchanged fresh extension
              have totalStill := holesStill_trans f g target.refs middleTarget.refs next.refs () still bodyStill fresh extension
              refine ⟨next, h, targetResult, ?_, related, nextStates, totalExtension, totalFresh, totalUnchanged, totalStill⟩
              rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgsRun]
              simp only [Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                targetFound, targetEnough]
              rw [BviSem.fixClock_evaluate, targetBodyRun]
              cases targetResult with
              | val values => rfl
              | err error =>
                cases error with
                | abort reason => rfl
                | raise payload =>
                  cases payload with
                  | exn value => rfl
                  | ret vals => exact False.elim (targetNoReturn vals rfl)

/-- Flapjack infrastructure: the non-extracted, handler-free call case of
the TMC singleton simulation, including worker hole filling. -/
theorem evaluate_call_no_handler_non_extracted {C F : Type} (loc ticks : Nat)
    (dest : Option Nat) (args : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.call ticks dest args none] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.call ticks dest args none))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (notExtracted : toBlockSource env1.length loc (.call ticks dest args none) = none)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.call ticks dest args none]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.call ticks dest args none) source target env1 env2 opt f loc result final := by
  have core := evaluate_call_no_handler_core loc ticks dest args source target env1 env2 opt f result final
    run notTypeError safe environments states weightIH clockIH
  refine ⟨core, ?_⟩
  intro locOpt _code
  constructor
  · intro wrapper rewrite
    simp [rewriteWrapperSource] at rewrite
  · intro optTrue holePtr c hole notFinal pointer
    have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
    obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ := core
    obtain ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩ :=
      FillHole.evaluate_fill_hole (.call ticks dest args none) f g env1 env2 source final target next result targetResult c holePtr
        run targetRun optEnv states extension related hole notFinal unchanged still fresh nextStates pointer
    simp only [rewriteWorkerSource, notExtracted]
    exact ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩

end Flapjack.Compiler.Backend.BviTmc.CallSimulation
