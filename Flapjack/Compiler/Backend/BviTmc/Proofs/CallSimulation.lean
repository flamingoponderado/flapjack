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

/-- Flapjack infrastructure: when a called body raises an exception, the
handler induction hypothesis applies at the body’s final clock.  The raised
values and environments are related at the map produced by the body. -/
theorem evaluate_call_handler_from_weight {C F : Type} (loc ticks destination : Nat)
    (args : List Bvi.Exp) (handler body targetBody : Bvi.Exp)
    (initial bodyStart bodyFinal : BviState (Nat × C) F) (bodyTarget : BviState C F)
    (callEnv targetCallEnv env1 env2 : List Value) (opt : Bool) (f g : HolFiniteMapExact Nat Nat)
    (raised : Value) (result : BviResult) (final : BviState (Nat × C) F)
    (bodyRun : evaluate [body] callEnv bodyStart = (.err (.raise (.exn raised)), bodyFinal))
    (bodyClock : bodyStart.clock ≤ initial.clock)
    (bodyCore : Core [targetBody] targetCallEnv g bodyTarget (.err (.raise (.exn raised))) bodyFinal)
    (handlerRun : evaluate [handler] (raised :: env1) bodyFinal = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (handlerSafe : noMutcons handler)
    (environments : envRel opt f env1 env2) (initialExtension : finiteSubmap f g)
    (weightIH : SmallerWeightIH (C := C) (F := F) initial.clock
      (expsWeight [.call ticks (some destination) args (some handler)])) :
    ∃ (next : BviState C F) (h : HolFiniteMapExact Nat Nat) (raisedTarget : Value),
      evaluate [targetBody] targetCallEnv bodyTarget = (.err (.raise (.exn raisedTarget)), next) ∧
      finiteSubmap g h ∧ onlyFresh g h bodyTarget.refs ∧
      holesUnchangedExcept g bodyTarget.refs next.refs ∅ ∧
      holesStillNotFinalised g bodyTarget.refs next.refs ∧
      SingletonPost handler bodyFinal next (raised :: env1) (raisedTarget :: env2) opt h loc result final := by
  obtain ⟨next, h, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ := bodyCore
  cases targetResult with
  | val values => simp [resultRel] at related
  | err error =>
    cases error with
    | abort reason => simp [resultRel, excRel] at related
    | raise payload =>
      cases payload with
      | ret values => simp [resultRel, excRel, eorRel] at related
      | exn raisedTarget =>
        have valuesRelated : valueRel h raised raisedTarget := by
          simpa [resultRel, excRel, eorRel] using related
        have envRelated : envRel opt h (raised :: env1) (raisedTarget :: env2) :=
          envRel_cons opt h env1 env2 raised raisedTarget
            (envRel_submap opt f h env1 env2 environments
              (fun key value found => extension key value (initialExtension key value found))) valuesRelated
        have finalClock : bodyFinal.clock ≤ initial.clock := by
          have bound := evaluate_clock_le [body] callEnv bodyStart
          rw [bodyRun] at bound
          exact Nat.le_trans bound bodyClock
        have weight : expsWeight [handler] < expsWeight [.call ticks (some destination) args (some handler)] := by
          simp [BviSem.expsWeight, BviSem.expWeight]
          omega
        have post := weightIH [handler] bodyFinal next (raised :: env1) (raisedTarget :: env2) opt h loc
          result final finalClock weight handlerRun (by simpa using handlerSafe) envRelated nextStates (by simp) notTypeError
        exact ⟨next, h, raisedTarget, targetRun, extension, fresh, unchanged, still, post.2 handler rfl⟩

/-- Flapjack infrastructure: a successful call that reaches its exception
handler returns that handler's result, which cannot be a return signal. -/
theorem call_handler_source_result {C F : Type} (ticks destination : Nat) (args : List Bvi.Exp)
    (handler body : Bvi.Exp) (env callEnv : List Value)
    (source middle bodyFinal handlerFinal final : BviState (Nat × C) F)
    (values : List Value) (raised : Value) (handlerResult result : BviResult)
    (run : evaluate [.call ticks (some destination) args (some handler)] env source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (argsRun : evaluate args env source = (.val values, middle))
    (found : findCode (some destination) values middle.code = some (callEnv, body))
    (enough : ¬middle.clock < ticks + 1)
    (bodyRun : evaluate [body] callEnv (decClock (ticks + 1) middle) = (.err (.raise (.exn raised)), bodyFinal))
    (handlerRun : evaluate [handler] (raised :: env) bodyFinal = (handlerResult, handlerFinal)) :
    (handlerResult, handlerFinal) = (result, final) ∧
      ∀ values, handlerResult ≠ .err (.raise (.ret values)) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, enough] at run
  rw [BviSem.fixClock_evaluate, bodyRun] at run
  simp only at run
  rw [handlerRun] at run
  have noReturn : ∀ values, handlerResult ≠ .err (.raise (.ret values)) := by
    intro values bad
    rw [bad] at run
    simp at run
    exact notTypeError run.1.symm
  refine ⟨?_, noReturn⟩
  cases handlerResult with
  | val values => simpa using run
  | err error =>
    cases error with
    | abort reason => simpa using run
    | raise payload =>
      cases payload with
      | exn value => simpa using run
      | ret values => exact False.elim (noReturn values rfl)

/-- Flapjack infrastructure: simulation of a direct call whose callee raises
and whose handler runs. The intermediate evaluations select this case; the
target evaluations and frame properties follow from the induction hypotheses. -/
theorem evaluate_call_handled_exception {C F : Type} (loc ticks destination : Nat)
    (args : List Bvi.Exp) (handler body : Bvi.Exp)
    (source middle bodyFinal final : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 callArgs : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (values : List Value) (raised : Value) (result : BviResult)
    (run : evaluate [.call ticks (some destination) args (some handler)] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (safe : noMutcons (.call ticks (some destination) args (some handler)))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (argsRun : evaluate args env1 source = (.val values, middle))
    (found : findCode (some destination) values middle.code = some (callArgs, body))
    (enough : ¬middle.clock < ticks + 1)
    (bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) = (.err (.raise (.exn raised)), bodyFinal))
    (handlerRun : evaluate [handler] (raised :: env1) bodyFinal = (result, final))
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks (some destination) args (some handler)]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    Core [.call ticks (some destination) args (some handler)] env2 f target result final := by
  have sourceResult := call_handler_source_result ticks destination args handler body env1 callArgs
    source middle bodyFinal final final values raised result result run notTypeError argsRun found enough bodyRun handlerRun
  have noReturn := sourceResult.2
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have argsSafe : ∀ e ∈ args, noMutcons e := fun e member => safe.1 ⟨e, member⟩
  have handlerSafe : noMutcons handler := safe.2
  have argsWeight : expsWeight args < expsWeight [.call ticks (some destination) args (some handler)] := by
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
      callArgs callArgs' false g bodyLoc (.err (.raise (.exn raised))) bodyFinal smaller bodyRun bodySafe callEnv decStates (by simp)
    have bodyCore : Core [body'] callArgs' g (decClock (ticks + 1) middleTarget)
        (.err (.raise (.exn raised))) bodyFinal := by
      by_cases same : body = body'
      · subst body'; exact bodyPost.1
      · obtain ⟨workerLoc, optimized, rewrite⟩ := changed same
        exact (bodyPost.2 workerLoc optimized).1 body' rewrite
    have bodyClock : (decClock (ticks + 1) middle).clock ≤ source.clock := Nat.le_of_lt smaller
    obtain ⟨next, h, raisedTarget, targetBodyRun, bodyExtension, bodyFresh, bodyUnchanged, bodyStill, handlerPost⟩ :=
      evaluate_call_handler_from_weight loc ticks destination args handler body body' source
        (decClock (ticks + 1) middle) bodyFinal (decClock (ticks + 1) middleTarget)
        callArgs callArgs' env1 env2 opt f g raised result final bodyRun bodyClock bodyCore handlerRun
        notTypeError handlerSafe environments extension weightIH
    obtain ⟨last, k, targetResult, targetHandlerRun, related, lastStates, handlerExtension,
      handlerFresh, handlerUnchanged, handlerStill⟩ := handlerPost.1
    have targetNoReturn := ForceSimulation.related_no_return k result targetResult related noReturn
    have argsDomain := BviProps.evaluate_refs_subset args env2 target middleTarget (.val values') targetArgsRun
    have bodyDomain := BviProps.evaluate_refs_subset [body'] callArgs' (decClock (ticks + 1) middleTarget) next
      (.err (.raise (.exn raisedTarget))) targetBodyRun
    have firstExtension : finiteSubmap f h := fun key value present => bodyExtension key value (extension key value present)
    have firstFresh := onlyFresh_trans f g h target.refs middleTarget.refs fresh bodyFresh argsDomain
    have firstUnchanged := holesUnchanged_trans f g target.refs middleTarget.refs next.refs ∅
      unchanged bodyUnchanged fresh extension
    have firstStill := holesStill_trans f g target.refs middleTarget.refs next.refs () still bodyStill fresh extension
    have allExtension : finiteSubmap f k := fun key value present => handlerExtension key value (firstExtension key value present)
    have allFresh := onlyFresh_trans f h k target.refs next.refs firstFresh handlerFresh
      (Set.Subset.trans argsDomain bodyDomain)
    have allUnchanged := holesUnchanged_trans f h target.refs next.refs last.refs ∅
      firstUnchanged handlerUnchanged firstFresh firstExtension
    have allStill := holesStill_trans f h target.refs next.refs last.refs () firstStill handlerStill firstFresh firstExtension
    refine ⟨last, k, targetResult, ?_, related, lastStates, allExtension, allFresh, allUnchanged, allStill⟩
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgsRun]
    simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, targetFound, targetEnough]
    rw [BviSem.fixClock_evaluate, targetBodyRun]
    simp only
    rw [targetHandlerRun]
    cases targetResult with
    | val values => rfl
    | err error =>
      cases error with
      | abort reason => rfl
      | raise payload =>
        cases payload with
        | exn value => rfl
        | ret values => exact False.elim (targetNoReturn values rfl)

/-- Flapjack infrastructure: the non-extracted worker and wrapper obligations
for a direct call whose callee raises and whose handler runs. -/
theorem evaluate_call_handled_exception_non_extracted {C F : Type} (loc ticks destination : Nat)
    (args : List Bvi.Exp) (handler body : Bvi.Exp)
    (source middle bodyFinal final : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 callArgs : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (values : List Value) (raised : Value) (result : BviResult)
    (run : evaluate [.call ticks (some destination) args (some handler)] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (safe : noMutcons (.call ticks (some destination) args (some handler)))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (argsRun : evaluate args env1 source = (.val values, middle))
    (found : findCode (some destination) values middle.code = some (callArgs, body))
    (enough : ¬middle.clock < ticks + 1)
    (bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) = (.err (.raise (.exn raised)), bodyFinal))
    (handlerRun : evaluate [handler] (raised :: env1) bodyFinal = (result, final))
    (notExtracted : toBlockSource env1.length loc (.call ticks (some destination) args (some handler)) = none)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks (some destination) args (some handler)]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.call ticks (some destination) args (some handler)) source target env1 env2 opt f loc result final := by
  have core := evaluate_call_handled_exception loc ticks destination args handler body source middle bodyFinal
    final target env1 env2 callArgs opt f values raised result run notTypeError safe environments states
    argsRun found enough bodyRun handlerRun weightIH clockIH
  refine ⟨core, ?_⟩
  intro locOpt _code
  constructor
  · intro wrapper rewrite
    simp [rewriteWrapperSource] at rewrite
  · intro optTrue holePtr c hole notFinal pointer
    have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
    obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ := core
    obtain ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩ :=
      FillHole.evaluate_fill_hole (.call ticks (some destination) args (some handler)) f g env1 env2 source
        final target next result targetResult c holePtr run targetRun optEnv states extension related hole
        notFinal unchanged still fresh nextStates pointer
    simp only [rewriteWorkerSource, notExtracted]
    exact ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩

/-- Flapjack infrastructure: adding a handler to a direct call preserves any
handler-free result that is not a raised exception. -/
theorem call_handler_inactive {C F : Type} (ticks destination : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env : List Value) (state final : BviState C F) (result : BviResult)
    (run : evaluate [.call ticks (some destination) args none] env state = (result, final))
    (noRaise : ∀ value, result ≠ .err (.raise (.exn value))) :
    evaluate [.call ticks (some destination) args (some handler)] env state = (result, final) := by
  cases argsRun : evaluate args env state with
  | mk argsResult middle =>
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run ⊢
    cases argsResult with
    | err error => simpa using run
    | val values =>
      cases found : findCode (some destination) values middle.code with
      | none => simpa [found] using run
      | some pair =>
        obtain ⟨callArgs, body⟩ := pair
        by_cases timeout : middle.clock < ticks + 1
        · simpa [found, timeout] using run
        · simp only [Option.isNone_some, Option.isSome_none, Option.isSome_some, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, found, timeout] at run ⊢
          rw [BviSem.fixClock_evaluate] at run ⊢
          cases bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) with
          | mk bodyResult bodyFinal =>
            cases bodyResult with
            | val values => simpa [bodyRun] using run
            | err error =>
              cases error with
              | abort reason => simpa [bodyRun] using run
              | raise payload =>
                cases payload with
                | exn value =>
                  simp [bodyRun] at run
                  exact False.elim (noRaise value run.1.symm)
                | ret values => simpa [bodyRun] using run

/-- Flapjack infrastructure: a result related to a non-raised source result
cannot itself be a raised exception. -/
theorem related_no_exception (f : HolFiniteMapExact Nat Nat) (source target : BviResult)
    (related : resultRel (List.Forall₂ (valueRel f)) (eorRel f) source target)
    (noRaise : ∀ value, source ≠ .err (.raise (.exn value))) :
    ∀ value, target ≠ .err (.raise (.exn value)) := by
  intro value eq
  subst target
  cases source with
  | val _ => simp [resultRel] at related
  | err error =>
    cases error with
    | abort _ => simp [resultRel, excRel] at related
    | raise payload =>
      cases payload with
      | ret _ => simp [resultRel, excRel, eorRel] at related
      | exn value' => exact noRaise value' rfl

/-- Flapjack infrastructure: a direct call with a handler is simulated when
its handler-free evaluation returns a result other than a raised exception. -/
theorem evaluate_call_handler_inactive_core {C F : Type} (loc ticks destination : Nat)
    (args : List Bvi.Exp) (handler : Bvi.Exp)
    (source final : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult)
    (run : evaluate [.call ticks (some destination) args none] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (noRaise : ∀ value, result ≠ .err (.raise (.exn value)))
    (safe : noMutcons (.call ticks (some destination) args (some handler)))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks (some destination) args (some handler)]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    Core [.call ticks (some destination) args (some handler)] env2 f target result final := by
  have safeNoHandler : noMutcons (.call ticks (some destination) args none) := by
    rw [noMutcons.eq_def] at safe ⊢
    simpa using safe.1
  have weightNoHandler : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks (some destination) args none]) := by
    intro xs s t a b o g l r last clock weight eval safeXs env st length notError
    apply weightIH xs s t a b o g l r last clock ?_ eval safeXs env st length notError
    simp only [BviSem.expsWeight, BviSem.expWeight] at weight ⊢
    omega
  obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ :=
    evaluate_call_no_handler_core loc ticks (some destination) args source target env1 env2 opt f result final
      run notTypeError safeNoHandler environments states weightNoHandler clockIH
  have targetNoRaise := related_no_exception g result targetResult related noRaise
  exact ⟨next, g, targetResult, call_handler_inactive ticks destination args handler env2 target next
    targetResult targetRun targetNoRaise, related, nextStates, extension, fresh, unchanged, still⟩

/-- Flapjack infrastructure: worker and wrapper simulation when a direct
call's handler-free evaluation produces a non-exception result. -/
theorem evaluate_call_handler_inactive_non_extracted {C F : Type} (loc ticks destination : Nat)
    (args : List Bvi.Exp) (handler : Bvi.Exp)
    (source final : BviState (Nat × C) F) (target : BviState C F)
    (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult)
    (run : evaluate [.call ticks (some destination) args none] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (noRaise : ∀ value, result ≠ .err (.raise (.exn value)))
    (safe : noMutcons (.call ticks (some destination) args (some handler)))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (notExtracted : toBlockSource env1.length loc (.call ticks (some destination) args (some handler)) = none)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks (some destination) args (some handler)]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.call ticks (some destination) args (some handler)) source target env1 env2 opt f loc result final := by
  have core := evaluate_call_handler_inactive_core loc ticks destination args handler source final target
    env1 env2 opt f result run notTypeError noRaise safe environments states weightIH clockIH
  have handledRun := call_handler_inactive ticks destination args handler env1 source final result run noRaise
  refine ⟨core, ?_⟩
  intro locOpt _code
  constructor
  · intro wrapper rewrite
    simp [rewriteWrapperSource] at rewrite
  · intro optTrue holePtr c hole notFinal pointer
    have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
    obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ := core
    obtain ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩ :=
      FillHole.evaluate_fill_hole (.call ticks (some destination) args (some handler)) f g env1 env2 source
        final target next result targetResult c holePtr handledRun targetRun optEnv states extension related hole
        notFinal unchanged still fresh nextStates pointer
    simp only [rewriteWorkerSource, notExtracted]
    exact ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩

/-- Flapjack infrastructure: argument errors propagate through a direct
handled call before the handler or callee can run. -/
theorem evaluate_call_handler_argument_error {C F : Type} (loc ticks destination : Nat)
    (args : List Bvi.Exp) (handler : Bvi.Exp) (source middle : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (argsRun : evaluate args env1 source = (.err error, middle))
    (notTypeError : (.err error : BviResult) ≠ .err (.abort .typeError))
    (safe : noMutcons (.call ticks (some destination) args (some handler)))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (notExtracted : toBlockSource env1.length loc (.call ticks (some destination) args (some handler)) = none)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks (some destination) args (some handler)])) :
    SingletonPost (.call ticks (some destination) args (some handler)) source target env1 env2 opt f loc
      (.err error) middle := by
  have argsSafe : ∀ e ∈ args, noMutcons e := by
    rw [noMutcons.eq_def] at safe
    exact fun e member => safe.1 ⟨e, member⟩
  have argsWeight : expsWeight args < expsWeight [.call ticks (some destination) args (some handler)] := by
    simp [BviSem.expsWeight, BviSem.expWeight]
    omega
  have run : evaluate [.call ticks (some destination) args (some handler)] env1 source = (.err error, middle) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp
  obtain ⟨next, g, targetResult, targetArgsRun, related, nextStates, extension, fresh, unchanged, still⟩ :=
    (weightIH args source target env1 env2 false f loc (.err error) middle (Nat.le_refl _) argsWeight argsRun
      argsSafe (envRel_relax opt f env1 env2 environments) states (by simp) notTypeError).1
  have core : Core [.call ticks (some destination) args (some handler)] env2 f target (.err error) middle := by
    cases targetResult with
    | val values => simp [resultRel] at related
    | err targetError =>
      refine ⟨next, g, .err targetError, ?_, related, nextStates, extension, fresh, unchanged, still⟩
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgsRun]
      simp
  refine ⟨core, ?_⟩
  intro locOpt _code
  constructor
  · intro wrapper rewrite
    simp [rewriteWrapperSource] at rewrite
  · intro optTrue holePtr c hole notFinal pointer
    have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
    obtain ⟨last, h, targetResult, targetRun, rel, lastStates, ext, only, unch, rest⟩ := core
    obtain ⟨fillResult, fillMap, fillState, fillRun, fillRel, state, fillExt, fillOnly, fillUnch, fillRest, filled⟩ :=
      FillHole.evaluate_fill_hole (.call ticks (some destination) args (some handler)) f h env1 env2 source
        middle target last (.err error) targetResult c holePtr run targetRun optEnv states ext rel hole
        notFinal unch rest only lastStates pointer
    simp only [rewriteWorkerSource, notExtracted]
    exact ⟨fillResult, fillMap, fillState, fillRun, fillRel, state, fillExt, fillOnly, fillUnch, fillRest, filled⟩

/-- Flapjack infrastructure: if a direct callee does not raise an exception,
the handler is not entered and the result is not an exception. -/
theorem call_handler_inactive_from_body {C F : Type} (ticks destination : Nat)
    (args : List Bvi.Exp) (handler body : Bvi.Exp) (env callArgs : List Value)
    (source middle bodyFinal final : BviState C F) (values : List Value)
    (bodyResult result : BviResult)
    (run : evaluate [.call ticks (some destination) args (some handler)] env source = (result, final))
    (argsRun : evaluate args env source = (.val values, middle))
    (found : findCode (some destination) values middle.code = some (callArgs, body))
    (enough : ¬middle.clock < ticks + 1)
    (bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) = (bodyResult, bodyFinal))
    (noBodyRaise : ∀ value, bodyResult ≠ .err (.raise (.exn value))) :
    evaluate [.call ticks (some destination) args none] env source = (result, final) ∧
      ∀ value, result ≠ .err (.raise (.exn value)) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, enough] at run
  rw [BviSem.fixClock_evaluate, bodyRun] at run
  have same : evaluate [.call ticks (some destination) args none] env source = (result, final) := by
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
    simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found, enough]
    rw [BviSem.fixClock_evaluate, bodyRun]
    cases bodyResult with
    | val values => simpa using run
    | err error =>
      cases error with
      | abort reason => simpa using run
      | raise payload =>
        cases payload with
        | exn value => exact False.elim (noBodyRaise value rfl)
        | ret values => simpa using run
  refine ⟨same, ?_⟩
  cases bodyResult with
  | val values => simp at run; rw [← run.1]; simp
  | err error =>
    cases error with
    | abort reason => simp at run; rw [← run.1]; simp
    | raise payload =>
      cases payload with
      | exn value => exact False.elim (noBodyRaise value rfl)
      | ret values => simp at run; rw [← run.1]; simp

/-- Flapjack infrastructure: complete non-extracted direct-call simulation
with an exception handler, from the shared structural and clock inductions. -/
theorem evaluate_call_handler_non_extracted {C F : Type} (loc ticks destination : Nat)
    (args : List Bvi.Exp) (handler : Bvi.Exp) (source final : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (result : BviResult)
    (run : evaluate [.call ticks (some destination) args (some handler)] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (safe : noMutcons (.call ticks (some destination) args (some handler)))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (notExtracted : toBlockSource env1.length loc (.call ticks (some destination) args (some handler)) = none)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks (some destination) args (some handler)]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.call ticks (some destination) args (some handler)) source target env1 env2 opt f loc result final := by
  cases argsRun : evaluate args env1 source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      have pair : (.err error, middle) = (result, final) := by
        have h := run
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at h
        simpa using h
      cases pair
      exact evaluate_call_handler_argument_error loc ticks destination args handler source final target env1 env2
        opt f error argsRun notTypeError safe environments states notExtracted weightIH
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
        · have noHandler : evaluate [.call ticks (some destination) args none] env1 source = (result, final) := by
            have h := run
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at h ⊢
            simpa [found, timeout] using h
          have noRaise : ∀ value, result ≠ .err (.raise (.exn value)) := by
            have h := run
            rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at h
            simp [found, timeout] at h
            rw [← h.1]
            simp
          exact evaluate_call_handler_inactive_non_extracted loc ticks destination args handler source final
            target env1 env2 opt f result noHandler notTypeError noRaise safe environments states notExtracted weightIH clockIH
        · cases bodyRun : evaluate [body] callArgs (decClock (ticks + 1) middle) with
          | mk bodyResult bodyFinal =>
            by_cases raises : ∃ value, bodyResult = .err (.raise (.exn value))
            · obtain ⟨raised, rfl⟩ := raises
              cases handlerRun : evaluate [handler] (raised :: env1) bodyFinal with
              | mk handlerResult handlerFinal =>
                have pair := (call_handler_source_result ticks destination args handler body env1 callArgs source middle
                  bodyFinal handlerFinal final values raised handlerResult result run notTypeError argsRun found timeout bodyRun handlerRun).1
                cases pair
                exact evaluate_call_handled_exception_non_extracted loc ticks destination args handler body source middle
                  bodyFinal final target env1 env2 callArgs opt f values raised result run notTypeError safe environments
                  states argsRun found timeout bodyRun handlerRun notExtracted weightIH clockIH
            · have noBodyRaise : ∀ value, bodyResult ≠ .err (.raise (.exn value)) := by
                intro value eq; exact raises ⟨value, eq⟩
              have ⟨noHandler, noRaise⟩ := call_handler_inactive_from_body ticks destination args handler body env1
                callArgs source middle bodyFinal final values bodyResult result run argsRun found timeout bodyRun noBodyRaise
              exact evaluate_call_handler_inactive_non_extracted loc ticks destination args handler source final target
                env1 env2 opt f result noHandler notTypeError noRaise safe environments states notExtracted weightIH clockIH

/-- Flapjack infrastructure: all non-extracted ordinary calls follow from
the shared structural and clock induction hypotheses. -/
theorem evaluate_call_non_extracted {C F : Type} (loc ticks : Nat) (destination : Option Nat)
    (args : List Bvi.Exp) (handler : Option Bvi.Exp) (source final : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (result : BviResult)
    (run : evaluate [.call ticks destination args handler] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (safe : noMutcons (.call ticks destination args handler))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (notExtracted : toBlockSource env1.length loc (.call ticks destination args handler) = none)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks destination args handler]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.call ticks destination args handler) source target env1 env2 opt f loc result final := by
  cases handler with
  | none =>
    exact evaluate_call_no_handler_non_extracted loc ticks destination args source target env1 env2 opt f result
      final run notTypeError safe environments states notExtracted weightIH clockIH
  | some handler =>
    cases destination with
    | none =>
      have bad : result = .err (.abort .typeError) := by
        have h := run
        simp [BviSem.evaluate] at h
        exact h.1.symm
      exact False.elim (notTypeError bad)
    | some destination =>
      exact evaluate_call_handler_non_extracted loc ticks destination args handler source final target env1 env2
        opt f result run notTypeError safe environments states notExtracted weightIH clockIH

/-- Flapjack infrastructure: the ordinary-call singleton simulation, covering
both extracted and non-extracted calls. -/
theorem evaluate_call_from_induction {C F : Type} (loc ticks : Nat) (destination : Option Nat)
    (args : List Bvi.Exp) (handler : Option Bvi.Exp) (source final : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (result : BviResult)
    (run : evaluate [.call ticks destination args handler] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (safe : noMutcons (.call ticks destination args handler))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock
      (expsWeight [.call ticks destination args handler]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.call ticks destination args handler) source target env1 env2 opt f loc result final := by
  cases extracted : toBlockSource env1.length loc (.call ticks destination args handler) with
  | none =>
    exact evaluate_call_non_extracted loc ticks destination args handler source final target env1 env2 opt f
      result run notTypeError safe environments states extracted weightIH clockIH
  | some pair =>
    obtain ⟨bindings, cb⟩ := pair
    exact evaluate_extracted_from_weight loc cb (.call ticks destination args handler) bindings source target env1 env2
      opt f result final run extracted notTypeError safe environments states weightIH clockIH

end Flapjack.Compiler.Backend.BviTmc.CallSimulation
