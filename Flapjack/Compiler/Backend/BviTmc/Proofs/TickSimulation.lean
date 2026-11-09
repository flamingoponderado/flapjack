import Flapjack.Compiler.Backend.BviTmc.Proofs.FillHole

/-! TMC simulation for the zero-clock tick case. -/
namespace Flapjack.Compiler.Backend.BviTmc.TickSimulation
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: the zero-clock branch of tick simulation, with
its induction measure and unnecessary safety premises omitted. -/
theorem evaluate_tick_timeout {C F : Type} (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [.tick body] env1 source = (result, final))
    (states : stateRel f source target)
    (zeroClock : source.clock = 0) :
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate [.tick body] env2 target = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, ([.tick body] : List Bvi.Exp).length = 1 ∧
            rewriteWrapperSource loc locOpt env1.length (.tick body) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (.tick body) = work ∧
          holEl i env2 = .refPtr false holePtr →
          ∃ (workResult : BviResult) (workMap : HolFiniteMapExact Nat Nat) (workState : BviState C F),
            evaluate [work] env2 target = (workResult, workState) ∧
            optResRel workMap result workResult ∧ stateRel workMap final workState ∧
            finiteSubmap f workMap ∧ onlyFresh f workMap target.refs ∧
            holesUnchangedExcept f target.refs workState.refs {holePtr} ∧
            holesStillNotFinalised f target.refs workState.refs ∧
            ∀ resValue, result = .val [resValue] →
              ∃ resValue', mutableBlockRel workMap target.refs (workState.refs.eraseEq holePtr) resValue resValue' ∧
                holeHasVal f env1 env2 workState.refs resValue')) := by
  have targetClock : target.clock = 0 := states.2.1.trans zeroClock
  have sourceRun : evaluate [.tick body] env1 source = (.err (.abort .timeoutError), source) := by
    simp [BviSem.evaluate, zeroClock]
  have same := run.symm.trans sourceRun
  cases same
  have targetRun (e : Bvi.Exp) : evaluate [.tick e] env2 target = (.err (.abort .timeoutError), target) := by
    simp [BviSem.evaluate, targetClock]
  refine ⟨target, f, .err (.abort .timeoutError), targetRun body, ?_, states, ?_,
    onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅,
    holesStill_refl f target.refs, ?_⟩
  · simp [resultRel, excRel]
  · intro key value found; exact found
  · intro locOpt _code
    constructor
    · intro wrap ⟨_, wrapper⟩
      simp only [rewriteWrapperSource] at wrapper
      cases h : rewriteWrapperSource loc locOpt env1.length body with
      | none => simp [h] at wrapper
      | some inner =>
        simp [h] at wrapper
        subst wrap
        refine ⟨target, f, .err (.abort .timeoutError), targetRun inner, ?_, states, ?_,
          onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs ∅,
          holesStill_refl f target.refs⟩
        · simp [resultRel, excRel]
        · intro key value found; exact found
    · intro _opt i j holePtr work ⟨_, _, _, _, worker, _⟩
      simp only [rewriteWorkerSource] at worker
      subst work
      refine ⟨.err (.abort .timeoutError), f, target, targetRun _, ?_, states, ?_,
        onlyFresh_refl f target.refs, holesUnchanged_refl f target.refs {holePtr},
        holesStill_refl f target.refs, ?_⟩
      · simp [optResRel, excRel]
      · intro key value found; exact found
      · intro _ impossible; cases impossible

/-- Flapjack infrastructure: the positive-clock tick induction step.  The
hypothesis is the simulation of the body at the decremented clock; the original
well-founded induction measure and unrelated safety premises are omitted. -/
theorem evaluate_tick_succ {C F : Type} (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [.tick body] env1 source = (result, final))
    (states : stateRel f source target) (positive : source.clock ≠ 0)
    (ih : evaluate [body] env1 (BviSem.decClock 1 source) = (result, final) →
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate [body] env2 (BviSem.decClock 1 target) = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, ([body] : List Bvi.Exp).length = 1 ∧
            rewriteWrapperSource loc locOpt env1.length (body) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 (BviSem.decClock 1 target) = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (body) = work ∧
          holEl i env2 = .refPtr false holePtr →
          ∃ (workResult : BviResult) (workMap : HolFiniteMapExact Nat Nat) (workState : BviState C F),
            evaluate [work] env2 (BviSem.decClock 1 target) = (workResult, workState) ∧
            optResRel workMap result workResult ∧ stateRel workMap final workState ∧
            finiteSubmap f workMap ∧ onlyFresh f workMap target.refs ∧
            holesUnchangedExcept f target.refs workState.refs {holePtr} ∧
            holesStillNotFinalised f target.refs workState.refs ∧
            ∀ resValue, result = .val [resValue] →
              ∃ resValue', mutableBlockRel workMap target.refs (workState.refs.eraseEq holePtr) resValue resValue' ∧
                holeHasVal f env1 env2 workState.refs resValue'))) :
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate [.tick body] env2 target = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, ([.tick body] : List Bvi.Exp).length = 1 ∧
            rewriteWrapperSource loc locOpt env1.length (.tick body) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (.tick body) = work ∧
          holEl i env2 = .refPtr false holePtr →
          ∃ (workResult : BviResult) (workMap : HolFiniteMapExact Nat Nat) (workState : BviState C F),
            evaluate [work] env2 target = (workResult, workState) ∧
            optResRel workMap result workResult ∧ stateRel workMap final workState ∧
            finiteSubmap f workMap ∧ onlyFresh f workMap target.refs ∧
            holesUnchangedExcept f target.refs workState.refs {holePtr} ∧
            holesStillNotFinalised f target.refs workState.refs ∧
            ∀ resValue, result = .val [resValue] →
              ∃ resValue', mutableBlockRel workMap target.refs (workState.refs.eraseEq holePtr) resValue resValue' ∧
                holeHasVal f env1 env2 workState.refs resValue')) := by
  have targetPositive : target.clock ≠ 0 := by simpa [states.2.1] using positive
  have childRun : evaluate [body] env1 (BviSem.decClock 1 source) = (result, final) := by
    simpa [BviSem.evaluate, positive] using run
  obtain ⟨next, nextMap, nextResult, targetRun, related, nextStates, extension, fresh,
    unchanged, still, optimised⟩ := ih childRun
  refine ⟨next, nextMap, nextResult, ?_, related, nextStates, extension, fresh,
    unchanged, still, ?_⟩
  · simpa [BviSem.evaluate, targetPositive] using targetRun
  · intro locOpt code
    obtain ⟨wrapperIH, workerIH⟩ := optimised locOpt code
    constructor
    · intro wrap ⟨_, wrapper⟩
      simp only [rewriteWrapperSource] at wrapper
      cases h : rewriteWrapperSource loc locOpt env1.length body with
      | none => simp [h] at wrapper
      | some inner =>
        simp [h] at wrapper
        subst wrap
        obtain ⟨wrapState, wrapMap, wrapResult, innerRun, rel, state, ext, only, unch, rest⟩ :=
          wrapperIH inner ⟨rfl, h⟩
        refine ⟨wrapState, wrapMap, wrapResult, ?_, rel, state, ext, only, unch, rest⟩
        simpa [BviSem.evaluate, targetPositive] using innerRun
    · intro optTrue i j holePtr work ⟨iEq, jEq, hole, notFinal, worker, ptr⟩
      simp only [rewriteWorkerSource] at worker
      subst work
      obtain ⟨workResult, workMap, workState, innerRun, rel, state, ext, only, unch, rest, filled⟩ :=
        workerIH optTrue i j holePtr _ ⟨iEq, jEq, hole, notFinal, rfl, ptr⟩
      refine ⟨workResult, workMap, workState, ?_, rel, state, ext, only, unch, rest, filled⟩
      simpa [BviSem.evaluate, targetPositive] using innerRun

/-- Flapjack infrastructure: the complete tick induction step, specialized to
one body induction hypothesis and omitting the original measure and safety
premises. -/
theorem evaluate_tick {C F : Type} (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [.tick body] env1 source = (result, final))
    (states : stateRel f source target)
    (ih : source.clock ≠ 0 → evaluate [body] env1 (BviSem.decClock 1 source) = (result, final) →
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate [body] env2 (BviSem.decClock 1 target) = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, ([body] : List Bvi.Exp).length = 1 ∧
            rewriteWrapperSource loc locOpt env1.length (body) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 (BviSem.decClock 1 target) = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (body) = work ∧
          holEl i env2 = .refPtr false holePtr →
          ∃ (workResult : BviResult) (workMap : HolFiniteMapExact Nat Nat) (workState : BviState C F),
            evaluate [work] env2 (BviSem.decClock 1 target) = (workResult, workState) ∧
            optResRel workMap result workResult ∧ stateRel workMap final workState ∧
            finiteSubmap f workMap ∧ onlyFresh f workMap target.refs ∧
            holesUnchangedExcept f target.refs workState.refs {holePtr} ∧
            holesStillNotFinalised f target.refs workState.refs ∧
            ∀ resValue, result = .val [resValue] →
              ∃ resValue', mutableBlockRel workMap target.refs (workState.refs.eraseEq holePtr) resValue resValue' ∧
                holeHasVal f env1 env2 workState.refs resValue'))) :
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate [.tick body] env2 target = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, ([.tick body] : List Bvi.Exp).length = 1 ∧
            rewriteWrapperSource loc locOpt env1.length (.tick body) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (.tick body) = work ∧
          holEl i env2 = .refPtr false holePtr →
          ∃ (workResult : BviResult) (workMap : HolFiniteMapExact Nat Nat) (workState : BviState C F),
            evaluate [work] env2 target = (workResult, workState) ∧
            optResRel workMap result workResult ∧ stateRel workMap final workState ∧
            finiteSubmap f workMap ∧ onlyFresh f workMap target.refs ∧
            holesUnchangedExcept f target.refs workState.refs {holePtr} ∧
            holesStillNotFinalised f target.refs workState.refs ∧
            ∀ resValue, result = .val [resValue] →
              ∃ resValue', mutableBlockRel workMap target.refs (workState.refs.eraseEq holePtr) resValue resValue' ∧
                holeHasVal f env1 env2 workState.refs resValue')) := by
  by_cases zero : source.clock = 0
  · exact evaluate_tick_timeout body source env1 result final opt f target env2 loc run states zero
  · exact evaluate_tick_succ body source env1 result final opt f target env2 loc run states zero (ih zero)

end Flapjack.Compiler.Backend.BviTmc.TickSimulation
