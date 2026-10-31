import Flapjack.Compiler.Backend.BviTmc.Proofs.CallSimulation

/-! Simulation of return-bearing calls in the TMC proof. -/
namespace Flapjack.Compiler.Backend.BviTmc.LetCallSimulation
open BviTmc BviSem BvlSem ListSimulation ClockHypothesis StructuralHypothesis SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: a returned list from a called body gives related
continuation environments and permits the smaller-weight induction at the
body's final clock. -/
theorem continuation_from_weight {C F : Type} (loc rets ticks destination : Nat)
    (args : List Bvi.Exp) (continuation body targetBody : Bvi.Exp)
    (initial bodyStart bodyFinal : BviState (Nat × C) F) (bodyTarget : BviState C F)
    (callEnv targetCallEnv env1 env2 : List Value) (opt : Bool) (f g : HolFiniteMapExact Nat Nat)
    (returned : List Value) (result : BviResult) (final : BviState (Nat × C) F)
    (bodyRun : evaluate [body] callEnv bodyStart = (.err (.raise (.ret returned)), bodyFinal))
    (bodyClock : bodyStart.clock ≤ initial.clock)
    (bodyCore : Core [targetBody] targetCallEnv g bodyTarget (.err (.raise (.ret returned))) bodyFinal)
    (continuationRun : evaluate [continuation] (returned ++ env1) bodyFinal = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (continuationSafe : noMutcons continuation)
    (environments : envRel opt f env1 env2) (initialExtension : finiteSubmap f g)
    (weightIH : SmallerWeightIH (C := C) (F := F) initial.clock
      (expsWeight [.letCall rets ticks destination args continuation])) :
    ∃ (next : BviState C F) (h : HolFiniteMapExact Nat Nat) (returnedTarget : List Value),
      evaluate [targetBody] targetCallEnv bodyTarget = (.err (.raise (.ret returnedTarget)), next) ∧
      returned.length = returnedTarget.length ∧ finiteSubmap g h ∧ onlyFresh g h bodyTarget.refs ∧
      holesUnchangedExcept g bodyTarget.refs next.refs ∅ ∧
      holesStillNotFinalised g bodyTarget.refs next.refs ∧
      Core [continuation] (returnedTarget ++ env2) h next result final := by
  obtain ⟨next, h, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ := bodyCore
  cases targetResult with
  | val values => simp [resultRel] at related
  | err error =>
    cases error with
    | abort reason => simp [resultRel, excRel] at related
    | raise payload =>
      cases payload with
      | exn value => simp [resultRel, excRel, eorRel] at related
      | ret returnedTarget =>
        have valuesRelated : List.Forall₂ (valueRel h) returned returnedTarget := by
          simpa [resultRel, excRel, eorRel] using related
        have envRelated : envRel false h (returned ++ env1) (returnedTarget ++ env2) :=
          envRel_append false h env1 env2 returned returnedTarget
            (envRel_relax opt h env1 env2 (envRel_submap opt f h env1 env2 environments
              (fun key value found => extension key value (initialExtension key value found)))) valuesRelated
        have finalClock : bodyFinal.clock ≤ initial.clock := by
          have bound := evaluate_clock_le [body] callEnv bodyStart
          rw [bodyRun] at bound
          exact Nat.le_trans bound bodyClock
        have weight : expsWeight [continuation] < expsWeight [.letCall rets ticks destination args continuation] := by
          simp [BviSem.expsWeight, BviSem.expWeight]
          omega
        have post := weightIH [continuation] bodyFinal next (returned ++ env1) (returnedTarget ++ env2)
          false h loc result final finalClock weight continuationRun (by simpa using continuationSafe)
          envRelated nextStates (by simp) notTypeError
        exact ⟨next, h, returnedTarget, targetRun, valuesRelated.length_eq, extension, fresh, unchanged, still, post.1⟩

/-- Flapjack infrastructure: simulation of a let-call that returns the
expected number of values and continues. -/
theorem evaluate_letcall_return {C F : Type} (loc rets ticks destination : Nat)
    (args : List Bvi.Exp) (continuation body : Bvi.Exp)
    (source middle bodyFinal final : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 callArgs : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (values returned : List Value) (result : BviResult)
    (notTypeError : result ≠ .err (.abort .typeError))
    (safe : noMutcons (.letCall rets ticks destination args continuation))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (argsRun : evaluate args env1 source = (.val values, middle))
    (found : findCode (some destination) values middle.code = some (callArgs, body))
    (enough : ¬middle.clock < ticks + 1)
    (bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) = (.err (.raise (.ret returned)), bodyFinal))
    (length : returned.length = rets)
    (continuationRun : evaluate [continuation] (returned ++ env1) bodyFinal = (result, final))
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.letCall rets ticks destination args continuation]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    Core [.letCall rets ticks destination args continuation] env2 f target result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have argsSafe : ∀ e ∈ args, noMutcons e := fun e member => safe.1 ⟨e, member⟩
  have argsWeight : expsWeight args < expsWeight [.letCall rets ticks destination args continuation] := by
    simp [BviSem.expsWeight, BviSem.expWeight]
    omega
  obtain ⟨middleTarget, g, targetArgsResult, targetArgsRun, argsRelated, middleStates,
    extension, fresh, unchanged, still⟩ :=
    (weightIH args source target env1 env2 false f loc (.val values) middle (Nat.le_refl _) argsWeight
      argsRun argsSafe (envRel_relax opt f env1 env2 environments) states (by simp) (by simp)).1
  cases targetArgsResult with
  | err error => simp [resultRel] at argsRelated
  | val values' =>
    obtain ⟨bodySafe, callArgs', body', bodyLoc, targetFound, callEnv, _, changed⟩ :=
      findCode_rel g values values' middle middleTarget (some destination) callArgs body found argsRelated middleStates
    have targetEnough : ¬middleTarget.clock < ticks + 1 := by simpa [middleStates.2.1] using enough
    have argsClock := BviSem.evaluate_clock_le args env1 source
    rw [argsRun] at argsClock
    dsimp only at argsClock
    have smaller : (decClock (ticks + 1) middle).clock < source.clock := by
      simp [BviSem.decClock]
      omega
    have decStates : stateRel g (decClock (ticks + 1) middle) (decClock (ticks + 1) middleTarget) := by
      simpa [BviSem.decClock, middleStates.2.1] using
        stateRel_with_clock (middle.clock - (ticks + 1)) g middle middleTarget middleStates
    have bodyPost := clockIH body (decClock (ticks + 1) middle) (decClock (ticks + 1) middleTarget)
      callArgs callArgs' false g bodyLoc (.err (.raise (.ret returned))) bodyFinal smaller bodyRun bodySafe callEnv decStates (by simp)
    have bodyCore : Core [body'] callArgs' g (decClock (ticks + 1) middleTarget)
        (.err (.raise (.ret returned))) bodyFinal := by
      by_cases same : body = body'
      · subst body'; exact bodyPost.1
      · obtain ⟨workerLoc, optimized, rewrite⟩ := changed same
        exact (bodyPost.2 workerLoc optimized).1 body' rewrite
    obtain ⟨next, h, returnedTarget, targetBodyRun, sameLength, bodyExtension, bodyFresh,
      bodyUnchanged, bodyStill, continuationCore⟩ :=
      continuation_from_weight loc rets ticks destination args continuation body body' source
        (decClock (ticks + 1) middle) bodyFinal (decClock (ticks + 1) middleTarget)
        callArgs callArgs' env1 env2 opt f g returned result final bodyRun (Nat.le_of_lt smaller) bodyCore
        continuationRun notTypeError safe.2 environments extension weightIH
    obtain ⟨last, k, targetResult, targetContinuationRun, related, lastStates, continuationExtension,
      continuationFresh, continuationUnchanged, continuationStill⟩ := continuationCore
    have argsDomain := BviProps.evaluate_refs_subset args env2 target middleTarget (.val values') targetArgsRun
    have bodyDomain := BviProps.evaluate_refs_subset [body'] callArgs' (decClock (ticks + 1) middleTarget) next
      (.err (.raise (.ret returnedTarget))) targetBodyRun
    have firstExtension : finiteSubmap f h := fun key value present => bodyExtension key value (extension key value present)
    have firstFresh := onlyFresh_trans f g h target.refs middleTarget.refs fresh bodyFresh argsDomain
    have firstUnchanged := holesUnchanged_trans f g target.refs middleTarget.refs next.refs ∅
      unchanged bodyUnchanged fresh extension
    have firstStill := holesStill_trans f g target.refs middleTarget.refs next.refs () still bodyStill fresh extension
    have allExtension : finiteSubmap f k := fun key value present => continuationExtension key value (firstExtension key value present)
    have allFresh := onlyFresh_trans f h k target.refs next.refs firstFresh continuationFresh
      (Set.Subset.trans argsDomain bodyDomain)
    have allUnchanged := holesUnchanged_trans f h target.refs next.refs last.refs ∅
      firstUnchanged continuationUnchanged firstFresh firstExtension
    have allStill := holesStill_trans f h target.refs next.refs last.refs () firstStill continuationStill firstFresh firstExtension
    refine ⟨last, k, targetResult, ?_, related, lastStates, allExtension, allFresh, allUnchanged, allStill⟩
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgsRun]
    simp only [targetFound, targetEnough, ↓reduceIte]
    rw [BviSem.fixClock_evaluate, targetBodyRun]
    simp only
    have targetLength : returnedTarget.length = rets := sameLength.symm.trans length
    simpa [targetLength] using targetContinuationRun

/-- Flapjack infrastructure: worker and wrapper simulation for a let-call
that returns the expected values and executes its continuation. -/
theorem evaluate_letcall_return_post {C F : Type} (loc rets ticks destination : Nat)
    (args : List Bvi.Exp) (continuation body : Bvi.Exp)
    (source middle bodyFinal final : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 callArgs : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (values returned : List Value) (result : BviResult)
    (notTypeError : result ≠ .err (.abort .typeError))
    (safe : noMutcons (.letCall rets ticks destination args continuation))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (argsRun : evaluate args env1 source = (.val values, middle))
    (found : findCode (some destination) values middle.code = some (callArgs, body))
    (enough : ¬middle.clock < ticks + 1)
    (bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) = (.err (.raise (.ret returned)), bodyFinal))
    (length : returned.length = rets)
    (continuationRun : evaluate [continuation] (returned ++ env1) bodyFinal = (result, final))
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.letCall rets ticks destination args continuation]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.letCall rets ticks destination args continuation) source target env1 env2 opt f loc result final := by
  have core := evaluate_letcall_return loc rets ticks destination args continuation body source middle bodyFinal
    final target env1 env2 callArgs opt f values returned result notTypeError safe environments states argsRun
    found enough bodyRun length continuationRun weightIH clockIH
  have run : evaluate [.letCall rets ticks destination args continuation] env1 source = (result, final) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp only [found, enough, ↓reduceIte]
    rw [BviSem.fixClock_evaluate, bodyRun]
    simpa [length] using continuationRun
  refine ⟨core, ?_⟩
  intro locOpt _code
  constructor
  · intro wrapper rewrite
    simp [rewriteWrapperSource] at rewrite
  · intro optTrue holePtr c hole notFinal pointer
    have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
    obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ := core
    obtain ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩ :=
      FillHole.evaluate_fill_hole (.letCall rets ticks destination args continuation) f g env1 env2 source
        final target next result targetResult c holePtr run targetRun optEnv states extension related hole
        notFinal unchanged still fresh nextStates pointer
    simp only [rewriteWorkerSource]
    exact ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩

/-- Flapjack infrastructure: when a direct call without a handler ends in a
non-type-error error, the corresponding let-call propagates the same error. -/
theorem letcall_of_call_error {C F : Type} (rets ticks destination : Nat) (args : List Bvi.Exp)
    (continuation : Bvi.Exp) (env : List Value) (state final : BviState C F)
    (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (run : evaluate [.call ticks (some destination) args none] env state = (.err error, final))
    (notTypeError : (.err error : BviResult) ≠ .err (.abort .typeError)) :
    evaluate [.letCall rets ticks destination args continuation] env state = (.err error, final) := by
  cases argsRun : evaluate args env state with
  | mk argsResult middle =>
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    cases argsResult with
    | err error => simpa using run
    | val values =>
      cases found : findCode (some destination) values middle.code with
      | none =>
        simp [found] at run
        exact False.elim (notTypeError (congrArg SemanticPrimitivesHOL.Result.err run.1.symm))
      | some pair =>
        obtain ⟨callArgs, body⟩ := pair
        by_cases timeout : middle.clock < ticks + 1
        · simpa [found, timeout] using run
        · simp only [Option.isNone_some, Option.isSome_none, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte, found, timeout] at run ⊢
          rw [BviSem.fixClock_evaluate] at run ⊢
          cases bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) with
          | mk bodyResult bodyFinal =>
            cases bodyResult with
            | val values => simp [bodyRun] at run
            | err bodyError =>
              cases bodyError with
              | abort reason => simpa [bodyRun] using run
              | raise payload =>
                cases payload with
                | exn value => simpa [bodyRun] using run
                | ret values =>
                  simp [bodyRun] at run
                  exact False.elim (notTypeError (congrArg SemanticPrimitivesHOL.Result.err run.1.symm))

/-- Flapjack infrastructure: simulation of let-calls that agree with a
handler-free call returning a non-type-error error. -/
theorem evaluate_letcall_error_post {C F : Type} (loc rets ticks destination : Nat)
    (args : List Bvi.Exp) (continuation : Bvi.Exp) (source final : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (run : evaluate [.call ticks (some destination) args none] env1 source = (.err error, final))
    (notTypeError : (.err error : BviResult) ≠ .err (.abort .typeError))
    (safe : noMutcons (.letCall rets ticks destination args continuation))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.letCall rets ticks destination args continuation]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.letCall rets ticks destination args continuation) source target env1 env2 opt f loc (.err error) final := by
  have safeCall : noMutcons (.call ticks (some destination) args none) := by
    rw [noMutcons.eq_def] at safe ⊢
    simpa using safe.1
  have weightCall : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks (some destination) args none]) := by
    intro xs s t a b o g l r last clock weight eval safeXs env st length notError
    apply weightIH xs s t a b o g l r last clock ?_ eval safeXs env st length notError
    simp only [BviSem.expsWeight, BviSem.expWeight] at weight ⊢
    omega
  obtain ⟨next, g, targetResult, targetCallRun, related, nextStates, extension, fresh, unchanged, still⟩ :=
    CallSimulation.evaluate_call_no_handler_core loc ticks (some destination) args source target env1 env2 opt f
      (.err error) final run notTypeError safeCall environments states weightCall clockIH
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    have targetNotTypeError : (.err targetError : BviResult) ≠ .err (.abort .typeError) := by
      intro bad
      have eq : targetError = .abort .typeError := SemanticPrimitivesHOL.Result.err.inj bad
      subst targetError
      cases error with
      | abort reason =>
        simp [resultRel, excRel] at related
        exact notTypeError (by simp [related])
      | raise payload => simp [resultRel, excRel] at related
    have targetRun := letcall_of_call_error rets ticks destination args continuation env2 target next
      targetError targetCallRun targetNotTypeError
    have sourceRun := letcall_of_call_error rets ticks destination args continuation env1 source final
      error run notTypeError
    have core : Core [.letCall rets ticks destination args continuation] env2 f target (.err error) final :=
      ⟨next, g, .err targetError, targetRun, related, nextStates, extension, fresh, unchanged, still⟩
    refine ⟨core, ?_⟩
    intro locOpt _code
    constructor
    · intro wrapper rewrite
      simp [rewriteWrapperSource] at rewrite
    · intro optTrue holePtr c hole notFinal pointer
      have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
      obtain ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩ :=
        FillHole.evaluate_fill_hole (.letCall rets ticks destination args continuation) f g env1 env2 source
          final target next (.err error) (.err targetError) c holePtr sourceRun targetRun optEnv states extension
          related hole notFinal unchanged still fresh nextStates pointer
      simp only [rewriteWorkerSource]
      exact ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩

/-- Flapjack infrastructure: a callee error other than a return signal is
propagated identically by a let-call and an ordinary call. -/
theorem call_error_of_letcall_body {C F : Type} (rets ticks destination : Nat)
    (args : List Bvi.Exp) (continuation body : Bvi.Exp) (env callArgs : List Value)
    (source middle bodyFinal final : BviState C F) (values : List Value)
    (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet) (result : BviResult)
    (run : evaluate [.letCall rets ticks destination args continuation] env source = (result, final))
    (argsRun : evaluate args env source = (.val values, middle))
    (found : findCode (some destination) values middle.code = some (callArgs, body))
    (enough : ¬middle.clock < ticks + 1)
    (bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) = (.err error, bodyFinal))
    (noReturn : ∀ values, error ≠ .raise (.ret values)) :
    (.err error, bodyFinal) = (result, final) ∧
      evaluate [.call ticks (some destination) args none] env source = (.err error, bodyFinal) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
  simp only [found, enough, ↓reduceIte] at run
  rw [BviSem.fixClock_evaluate, bodyRun] at run
  have callRun : evaluate [.call ticks (some destination) args none] env source = (.err error, bodyFinal) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp only [Option.isNone_some, Option.isSome_none, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, found, enough]
    rw [BviSem.fixClock_evaluate, bodyRun]
    cases error with
    | abort reason => rfl
    | raise payload =>
      cases payload with
      | exn value => rfl
      | ret values => exact False.elim (noReturn values rfl)
  refine ⟨?_, callRun⟩
  cases error with
  | abort reason => simpa using run
  | raise payload =>
    cases payload with
    | exn value => simpa using run
    | ret values => exact False.elim (noReturn values rfl)

/-- Flapjack infrastructure: the let-call singleton simulation follows from
the shared structural and clock induction hypotheses. -/
theorem evaluate_letcall_from_induction {C F : Type} (loc rets ticks destination : Nat)
    (args : List Bvi.Exp) (continuation : Bvi.Exp) (source final : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (result : BviResult)
    (run : evaluate [.letCall rets ticks destination args continuation] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (safe : noMutcons (.letCall rets ticks destination args continuation))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.letCall rets ticks destination args continuation]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.letCall rets ticks destination args continuation) source target env1 env2 opt f loc result final := by
  cases argsRun : evaluate args env1 source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      have pair : (.err error, middle) = (result, final) := by
        have h := run
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at h
        simpa using h
      cases pair
      have callRun : evaluate [.call ticks (some destination) args none] env1 source = (.err error, final) := by
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
        simp
      exact evaluate_letcall_error_post loc rets ticks destination args continuation source final target env1 env2
        opt f error callRun notTypeError safe environments states weightIH clockIH
    | val values =>
      cases found : findCode (some destination) values middle.code with
      | none =>
        have bad : result = .err (.abort .typeError) := by
          have h := run
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at h
          simp [found] at h
          exact h.1.symm
        exact False.elim (notTypeError bad)
      | some pair =>
        obtain ⟨callArgs, body⟩ := pair
        by_cases timeout : middle.clock < ticks + 1
        · have pair : (.err (.abort .timeoutError), { middle with clock := 0 }) = (result, final) := by
            have h := run
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at h
            simpa [found, timeout] using h
          cases pair
          have callRun : evaluate [.call ticks (some destination) args none] env1 source =
              (.err (.abort .timeoutError), { middle with clock := 0 }) := by
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
            simp [found, timeout]
          exact evaluate_letcall_error_post loc rets ticks destination args continuation source { middle with clock := 0 } target env1 env2
            opt f (.abort .timeoutError) callRun notTypeError safe environments states weightIH clockIH
        · cases bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) with
          | mk bodyResult bodyFinal =>
            cases bodyResult with
            | val values =>
              have bad : result = .err (.abort .typeError) := by
                have h := run
                rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at h
                simp only [found, timeout, ↓reduceIte] at h
                rw [BviSem.fixClock_evaluate, bodyRun] at h
                simp at h
                exact h.1.symm
              exact False.elim (notTypeError bad)
            | err error =>
              by_cases returns : ∃ returned, error = .raise (.ret returned)
              · obtain ⟨returned, rfl⟩ := returns
                by_cases length : returned.length = rets
                · have continuationRun : evaluate [continuation] (returned ++ env1) bodyFinal = (result, final) := by
                    have h := run
                    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at h
                    simp only [found, timeout, ↓reduceIte] at h
                    rw [BviSem.fixClock_evaluate, bodyRun] at h
                    simpa [length] using h
                  exact evaluate_letcall_return_post loc rets ticks destination args continuation body source middle
                    bodyFinal final target env1 env2 callArgs opt f values returned result notTypeError safe environments
                    states argsRun found timeout bodyRun length continuationRun weightIH clockIH
                · have bad : result = .err (.abort .typeError) := by
                    have h := run
                    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at h
                    simp only [found, timeout, ↓reduceIte] at h
                    rw [BviSem.fixClock_evaluate, bodyRun] at h
                    simp [length] at h
                    exact h.1.symm
                  exact False.elim (notTypeError bad)
              · have noReturn : ∀ returned, error ≠ .raise (.ret returned) := by
                  intro returned eq; exact returns ⟨returned, eq⟩
                obtain ⟨pair, callRun⟩ := call_error_of_letcall_body rets ticks destination args continuation body
                  env1 callArgs source middle bodyFinal final values error result run argsRun found timeout bodyRun noReturn
                cases pair
                exact evaluate_letcall_error_post loc rets ticks destination args continuation source final target env1 env2
                  opt f error callRun notTypeError safe environments states weightIH clockIH

end Flapjack.Compiler.Backend.BviTmc.LetCallSimulation
