module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.StructuralHypothesis
public import Flapjack.Compiler.Backend.BviTmc.Proofs.IfAssembly
public import Flapjack.Compiler.Backend.BviTmc.Proofs.LetAssembly

@[expose] public section

/-! Singleton expression cases for the TMC structural induction. -/
namespace Flapjack.Compiler.Backend.BviTmc.StructuralCases
open BviTmc BviSem BvlSem ListSimulation ClockHypothesis StructuralHypothesis SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: the return case follows from the smaller-weight
argument-list hypothesis. -/
theorem evaluate_return_from_weight {C F : Type} (loc : Nat) (args : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.return args] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.return args))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.return args])) :
    SingletonPost (.return args) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have argsSafe : ∀ e ∈ args, noMutcons e := fun e member => safe ⟨e, member⟩
  have weight : expsWeight args < expsWeight [.return args] := by
    simp [BviSem.expsWeight, BviSem.expWeight]
    omega
  have childIH : ∀ childResult childFinal,
      evaluate args env1 source = (childResult, childFinal) →
      childResult ≠ .err (.abort .typeError) → Core args env2 f target childResult childFinal := by
    intro childResult childFinal childRun childSafe
    exact (ih args source target env1 env2 false f loc childResult childFinal (Nat.le_refl _) weight childRun argsSafe
      (envRel_relax opt f env1 env2 environments) states (by simp) childSafe).1
  have finish (sourceError targetError : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
      (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat)
      (sourceResult : result = .err sourceError)
      (targetRun : evaluate [.return args] env2 target = (.err targetError, next))
      (related : excRel (eorRel nextMap) sourceError targetError)
      (states : stateRel nextMap final next) (extension : f.submap nextMap)
      (fresh : onlyFresh f nextMap target.refs)
      (unchanged : holesUnchangedExcept f target.refs next.refs ∅)
      (still : holesStillNotFinalised f target.refs next.refs) :
      SingletonPost (.return args) source target env1 env2 opt f loc result final := by
    subst result
    refine ⟨⟨next, nextMap, .err targetError, targetRun, related, states, extension, fresh,
      unchanged, still⟩, ?_⟩
    intro locOpt _code
    constructor
    · intro wrap wrapper
      simp [rewriteWrapperSource] at wrapper
    · intro _opt holePtr _c _hole _notFinal _pointer
      simp only [rewriteWorkerSource]
      have workRun := FillHole.evaluate_fillHole_error (.return args)
        env1.length (env1.length + 1) env2 target next targetError targetRun
      refine ⟨.err targetError, nextMap, next, workRun, related, states, extension, fresh,
        holesUnchanged_subset f target.refs next.refs ∅ {holePtr} ⟨unchanged, by simp⟩, still, ?_⟩
      intro _ impossible; cases impossible
  cases childRun : evaluate args env1 source with
  | mk childResult childFinal =>
    have childSafe : childResult ≠ .err (.abort .typeError) := by
      intro bad
      subst childResult
      simp [BviSem.evaluate, childRun] at run
      exact notTypeError run.1.symm
    obtain ⟨next, nextMap, nextResult, targetRun, related, states, extension, fresh,
      unchanged, still⟩ := childIH childResult childFinal childRun childSafe
    cases childResult with
    | err error =>
      cases nextResult with
      | val values => simp [resultRel] at related
      | err error' =>
        have eq : (.err error, childFinal) = (result, final) := by
          simpa [BviSem.evaluate, childRun] using run
        cases eq
        apply finish error error' next nextMap rfl _ related states extension fresh unchanged still
        simp [BviSem.evaluate, targetRun]
    | val values =>
      cases nextResult with
      | err error => simp [resultRel] at related
      | val values' =>
        have eq : (.err (.raise (.ret values)), childFinal) = (result, final) := by
          simpa [BviSem.evaluate, childRun] using run
        cases eq
        apply finish (.raise (.ret values)) (.raise (.ret values')) next nextMap rfl _
          related states extension fresh unchanged still
        simp [BviSem.evaluate, targetRun]
/-- Flapjack infrastructure: the raise case follows from the smaller-weight
body induction hypothesis. -/
theorem evaluate_raise_from_weight {C F : Type} (loc : Nat) (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.raise body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.raise body))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.raise body])) :
    SingletonPost (.raise body) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have weight : expsWeight [body] < expsWeight [.raise body] := by
    simp [BviSem.expsWeight, BviSem.expWeight]
  have childIH : ∀ childResult childFinal,
      evaluate [body] env1 source = (childResult, childFinal) →
      childResult ≠ .err (.abort .typeError) → Core [body] env2 f target childResult childFinal := by
    intro childResult childFinal childRun childSafe
    exact (ih [body] source target env1 env2 false f loc childResult childFinal (Nat.le_refl _) weight childRun
      (by simpa using safe) (envRel_relax opt f env1 env2 environments) states (by simp) childSafe).1
  have finish (sourceError targetError : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
      (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat)
      (sourceResult : result = .err sourceError)
      (targetRun : evaluate [.raise body] env2 target = (.err targetError, next))
      (related : excRel (eorRel nextMap) sourceError targetError)
      (states : stateRel nextMap final next) (extension : f.submap nextMap)
      (fresh : onlyFresh f nextMap target.refs)
      (unchanged : holesUnchangedExcept f target.refs next.refs ∅)
      (still : holesStillNotFinalised f target.refs next.refs) :
      SingletonPost (.raise body) source target env1 env2 opt f loc result final := by
    subst result
    refine ⟨⟨next, nextMap, .err targetError, targetRun, related, states, extension, fresh,
      unchanged, still⟩, ?_⟩
    intro locOpt _code
    constructor
    · intro wrap wrapper
      simp [rewriteWrapperSource] at wrapper
    · intro _opt holePtr _c _hole _notFinal _pointer
      simp only [rewriteWorkerSource]
      refine ⟨.err targetError, nextMap, next, targetRun, related, states, extension, fresh,
        holesUnchanged_subset f target.refs next.refs ∅ {holePtr} ⟨unchanged, by simp⟩, still, ?_⟩
      intro _ impossible; cases impossible
  cases childRun : evaluate [body] env1 source with
  | mk childResult childFinal =>
    have childSafe : childResult ≠ .err (.abort .typeError) := by
      intro bad
      subst childResult
      simp [BviSem.evaluate, childRun] at run
      exact notTypeError run.1.symm
    obtain ⟨next, nextMap, nextResult, targetRun, related, states, extension, fresh,
      unchanged, still⟩ := childIH childResult childFinal childRun childSafe
    cases childResult with
    | err error =>
      cases nextResult with
      | val values => simp [resultRel] at related
      | err error' =>
        have eq : (.err error, childFinal) = (result, final) := by
          simpa [BviSem.evaluate, childRun] using run
        cases eq
        apply finish error error' next nextMap rfl _ related states extension fresh unchanged still
        simp [BviSem.evaluate, targetRun]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton body env1 source childFinal values childRun
      cases nextResult with
      | err error => simp [resultRel] at related
      | val values' =>
        obtain ⟨value', rfl⟩ := evaluate_singleton body env2 target next values' targetRun
        have valueRelated : valueRel nextMap value value' := by
          simp only [resultRel] at related
          cases related with
          | cons h _ => exact h
        have eq : (.err (.raise (.exn value)), childFinal) = (result, final) := by
          rw [BviSem.evaluate, childRun] at run
          exact run
        cases eq
        apply finish (.raise (.exn value)) (.raise (.exn value')) next nextMap rfl _
          valueRelated states extension fresh unchanged still
        rw [BviSem.evaluate, targetRun]
        rfl

/-- Flapjack infrastructure: the tick case follows from the smaller-clock
singleton hypothesis. -/
theorem evaluate_tick_from_clock {C F : Type} (loc : Nat) (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.tick body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.tick body))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.tick body) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  by_cases zeroClock : source.clock = 0
  · have targetClock : target.clock = 0 := states.2.1.trans zeroClock
    have sourceRun : evaluate [.tick body] env1 source = (.err (.abort .timeoutError), source) := by
      simp [BviSem.evaluate, zeroClock]
    have same := run.symm.trans sourceRun
    cases same
    have targetRun (e : Bvi.Exp) :
        evaluate [.tick e] env2 target = (.err (.abort .timeoutError), target) := by
      simp [BviSem.evaluate, targetClock]
    refine ⟨?_, ?_⟩
    · refine ⟨target, f, .err (.abort .timeoutError), targetRun body, ?_, states,
        (fun _ _ found => found), onlyFresh_refl f target.refs,
        holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
      simp [resultRel, excRel]
    · intro locOpt _code
      constructor
      · intro wrap wrapper
        simp only [rewriteWrapperSource] at wrapper
        cases h : rewriteWrapperSource loc locOpt env1.length body with
        | none => simp [h] at wrapper
        | some inner =>
          simp [h] at wrapper
          subst wrap
          refine ⟨target, f, .err (.abort .timeoutError), targetRun inner, ?_, states,
            (fun _ _ found => found), onlyFresh_refl f target.refs,
            holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
          simp [resultRel, excRel]
      · intro _opt holePtr _c _hole _notFinal _pointer
        simp only [rewriteWorkerSource]
        refine ⟨.err (.abort .timeoutError), f, target, targetRun _, ?_, states,
          (fun _ _ found => found), onlyFresh_refl f target.refs,
          holesUnchanged_refl f target.refs {holePtr}, holesStill_refl f target.refs, ?_⟩
        · simp [optResRel, excRel]
        · intro _ impossible; cases impossible
  · have targetPositive : target.clock ≠ 0 := by simpa [states.2.1] using zeroClock
    have bodyRun : evaluate [body] env1 (BviSem.decClock 1 source) = (result, final) := by
      simpa [BviSem.evaluate, zeroClock] using run
    have smaller : (BviSem.decClock 1 source).clock < source.clock := by
      simp [BviSem.decClock]
      omega
    have decStates : stateRel f (BviSem.decClock 1 source) (BviSem.decClock 1 target) := by
      simpa [BviSem.decClock, states.2.1] using stateRel_with_clock (source.clock - 1) f source target states
    have post := ih body (BviSem.decClock 1 source) (BviSem.decClock 1 target) env1 env2 opt f loc result final
      smaller bodyRun safe environments decStates notTypeError
    obtain ⟨⟨next, nextMap, nextResult, targetRun, related, nextStates, extension, fresh,
      unchanged, still⟩, optimised⟩ := post
    refine ⟨⟨next, nextMap, nextResult, ?_, related, nextStates, extension, fresh, unchanged, still⟩, ?_⟩
    · simpa [BviSem.evaluate, targetPositive] using targetRun
    · intro locOpt code
      obtain ⟨wrapperIH, workerIH⟩ := optimised locOpt code
      constructor
      · intro wrap wrapper
        simp only [rewriteWrapperSource] at wrapper
        cases h : rewriteWrapperSource loc locOpt env1.length body with
        | none => simp [h] at wrapper
        | some inner =>
          simp [h] at wrapper
          subst wrap
          obtain ⟨wrapState, wrapMap, wrapResult, innerRun, rel, state, ext, only, unch, rest⟩ :=
            wrapperIH inner h
          refine ⟨wrapState, wrapMap, wrapResult, ?_, rel, state, ext, only, unch, rest⟩
          simpa [BviSem.evaluate, targetPositive] using innerRun
      · intro optTrue holePtr c hole notFinal pointer
        simp only [rewriteWorkerSource]
        obtain ⟨workResult, workMap, workState, innerRun, rel, state, ext, only, unch, rest, filled⟩ :=
          workerIH optTrue holePtr c hole notFinal pointer
        refine ⟨workResult, workMap, workState, ?_, rel, state, ext, only, unch, rest, filled⟩
        simpa [BviSem.evaluate, targetPositive] using innerRun

/-- Flapjack infrastructure: the conditional case follows from the common
smaller-weight induction, including the selected branch's clock bound. -/
theorem evaluate_if_from_weight {C F : Type} (loc : Nat) (condition yes no : Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.ifThenElse condition yes no] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.ifThenElse condition yes no))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.ifThenElse condition yes no])) :
    SingletonPost (.ifThenElse condition yes no) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have conditionWeight : expsWeight [condition] < expsWeight [.ifThenElse condition yes no] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  have yesWeight : expsWeight [yes] < expsWeight [.ifThenElse condition yes no] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  have noWeight : expsWeight [no] < expsWeight [.ifThenElse condition yes no] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  apply IfAssembly.evaluate_if condition yes no source env1 result final opt f target env2 loc
    run notTypeError environments
  · intro r mid conditionRun noError
    exact (ih [condition] source target env1 env2 false f loc r mid (Nat.le_refl _) conditionWeight conditionRun
      (by simpa using safe.1) (envRel_relax opt f env1 env2 environments) states (by simp) noError).1
  · intro branch mid g t ⟨conditionResult, conditionRun⟩ selected branchRun env nextStates
    have clock := evaluate_clock_le [condition] env1 source
    rw [conditionRun] at clock
    have weight : expsWeight [branch] < expsWeight [.ifThenElse condition yes no] := by
      rcases selected with rfl | rfl
      · exact yesWeight
      · exact noWeight
    have branchSafe : noMutcons branch := by
      rcases selected with rfl | rfl
      · exact safe.2.1
      · exact safe.2.2
    exact (ih [branch] mid t env1 env2 opt g loc result final clock weight branchRun
      (by simpa using branchSafe) env nextStates (by simp) notTypeError).2 branch rfl

/-- Flapjack infrastructure: the let case follows from the common
smaller-weight induction for the bindings and body. -/
theorem evaluate_let_from_weight {C F : Type} (loc : Nat) (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.let bindings body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.let bindings body))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.let bindings body])) :
    SingletonPost (.let bindings body) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have bindingsWeight : expsWeight bindings < expsWeight [.let bindings body] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  have bodyWeight : expsWeight [body] < expsWeight [.let bindings body] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  have bindingsSafe : ∀ e ∈ bindings, noMutcons e := fun e member => safe.1 ⟨e, member⟩
  apply LetAssembly.evaluate_let bindings body source env1 result final opt f target env2 loc
    run notTypeError environments
  · intro r mid bindingsRun noError
    exact (ih bindings source target env1 env2 false f loc r mid (Nat.le_refl _) bindingsWeight bindingsRun
      bindingsSafe (envRel_relax opt f env1 env2 environments) states (by simp) noError).1
  · intro values values' mid g t bindingsRun bodyRun env nextStates
    have clock := evaluate_clock_le bindings env1 source
    rw [bindingsRun] at clock
    exact (ih [body] mid t (values ++ env1) (values' ++ env2) opt g loc result final clock bodyWeight bodyRun
      (by simpa using safe.2) env nextStates (by simp) notTypeError).2 body rfl

end Flapjack.Compiler.Backend.BviTmc.StructuralCases
