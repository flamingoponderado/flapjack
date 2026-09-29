import Flapjack.Pancake.CrepToLoop.Proofs.SemanticsWrapper
import Flapjack.Pancake.Semantics.LoopSemStateExact.Semantics
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact

/-!
# `crep_to_loopProof` loop semantics wrapper case

This is the HOL-native `loop_sem_is_wrapper` case at
`cakeml/pancake/proofs/crep_to_loopProofScript.sml:4178-4210`.  It is kept in
its own case module so the pass-result wrapper and sibling Crep case can evolve
without theorem-body conflicts.
-/

namespace Flapjack

namespace LoopSemIsWrapperFiniteSupport

/-- Same-module witness for the `globals` finite-support translation used by
    `loopSemIsWrapper` (re-exports the checked exact `loopSem` state roundtrip). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopSemIsWrapperFiniteSupport

private def loopSemOutcomeOf {width : Nat} [NeZero width] :
    Option (LoopSemStateFiniteExact.LoopResultExact width) → Option HolOutcome
  | some (.finalFfi event) => some (.ffiOutcome event)
  | some (.result _) => some .success
  | _ => none

private def loopSemWrapperResult {width : Nat} [NeZero width] :
    Option (LoopSemStateFiniteExact.LoopResultExact width) →
      CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFfi event) => .CompleteResult (.ffiOutcome event)
  | some (.result _) => .CompleteResult .success
  | _ => .RunError

private theorem loopSemWrapperResult_complete_iff {width : Nat} [NeZero width]
    (result : Option (LoopSemStateFiniteExact.LoopResultExact width)) (outcome : HolOutcome) :
    loopSemWrapperResult result = .CompleteResult outcome ↔
      loopSemOutcomeOf result = some outcome := by
  cases result with
  | none => simp [loopSemWrapperResult, loopSemOutcomeOf]
  | some result => cases result <;> simp [loopSemWrapperResult, loopSemOutcomeOf]

private theorem loopSemWrapperResult_error_iff {width : Nat} [NeZero width]
    (result : Option (LoopSemStateFiniteExact.LoopResultExact width)) :
    loopSemWrapperResult result = .RunError ↔
      match result with
      | some .timeOut | some (.finalFfi _) | some (.result _) => False
      | _ => True := by
  cases result with
  | none => simp [loopSemWrapperResult]
  | some result => cases result <;> simp [loopSemWrapperResult]

private theorem loopSemOutcomeOf_eq_some_iff {width : Nat} [NeZero width]
    (result : Option (LoopSemStateFiniteExact.LoopResultExact width)) (outcome : HolOutcome) :
    (match result, outcome with
      | some (.finalFfi event), outcome => outcome = .ffiOutcome event
      | some (.result _), outcome => outcome = .success
      | _, _ => False) ↔ loopSemOutcomeOf result = some outcome := by
  cases result with
  | none => simp [loopSemOutcomeOf]
  | some result => cases result <;> simp [loopSemOutcomeOf, eq_comm]

private def loopSemForbiddenResult {width : Nat} [NeZero width]
    (result : Option (LoopSemStateFiniteExact.LoopResultExact width)) : Prop :=
  match result with
  | some .timeOut | some (.finalFfi _) | some (.result _) => False
  | _ => True

private def loopSemWrapperInput {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat) :
    Nat → CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent :=
  let prog : HolLoopProg width := .call none (some start) [] none
  fun clock => Prod.map loopSemWrapperResult (fun state => state.ffi.ioEvents)
    (LoopSemStateFiniteExact.evaluate prog { s with clock := clock })

private def loopSemWrapperSuccessfulObservation {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat) (result : HolBehaviour) : Prop :=
  ∃ clock outcome events,
    loopSemWrapperInput s start clock = (.CompleteResult outcome, events) ∧
      result = .terminate outcome events

private def loopSemWrapperHasErrorRun {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat) : Prop :=
  ∃ clock events, loopSemWrapperInput s start clock = (.RunError, events)

private def loopSemSuccessfulObservation {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat) (result : HolBehaviour) : Prop :=
  ∃ clock finalState runResult outcome,
    LoopSemStateFiniteExact.evaluate (.call none (some start) [] none)
        { s with clock := clock } = (runResult, finalState) ∧
      (match runResult, outcome with
       | some (.finalFfi event), outcome => outcome = .ffiOutcome event
       | some (.result _), outcome => outcome = .success
       | _, _ => False) ∧
      result = .terminate outcome finalState.ffi.ioEvents

private theorem loopSemForbiddenRun_iff_wrapperErrorRun {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat) :
    (∃ clock, loopSemForbiddenResult
      (LoopSemStateFiniteExact.evaluate (.call none (some start) [] none)
        { s with clock := clock }).1) ↔ loopSemWrapperHasErrorRun s start := by
  simp [loopSemWrapperHasErrorRun, loopSemWrapperInput, loopSemForbiddenResult,
    loopSemWrapperResult_error_iff, Prod.map]

private theorem loopSemSuccessfulObservation_iff_wrapper {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat) (result : HolBehaviour) :
    loopSemSuccessfulObservation s start result ↔
      loopSemWrapperSuccessfulObservation s start result := by
  constructor
  · rintro ⟨clock, finalState, runResult, outcome, hrun, hOutcome, hresult⟩
    have hOutcome' := (loopSemOutcomeOf_eq_some_iff runResult outcome).mp hOutcome
    have hComplete : loopSemWrapperResult runResult = .CompleteResult outcome :=
      (loopSemWrapperResult_complete_iff runResult outcome).mpr hOutcome'
    refine ⟨clock, outcome, finalState.ffi.ioEvents, ?_, hresult⟩
    simp [loopSemWrapperInput, hrun, hComplete]
  · rintro ⟨clock, outcome, events, hinput, hresult⟩
    cases hrun : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none)
        { s with clock := clock } with
    | mk runResult finalState =>
      have hpair : loopSemWrapperResult runResult = .CompleteResult outcome ∧
          finalState.ffi.ioEvents = events := by
        simpa [loopSemWrapperInput, hrun, Prod.map] using hinput
      have hOutcome : loopSemOutcomeOf runResult = some outcome :=
        (loopSemWrapperResult_complete_iff runResult outcome).mp hpair.1
      refine ⟨clock, finalState, runResult, outcome, hrun,
        (loopSemOutcomeOf_eq_some_iff runResult outcome).mpr hOutcome, ?_⟩
      simpa [hpair.2] using hresult

private theorem loopEvaluateSuccessfulObservation_unique {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start clock₁ clock₂ : Nat)
    (runResult₁ runResult₂ : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (finalState₁ finalState₂ : LoopSemStateFiniteExact width F)
    (h₁ : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none)
      { s with clock := clock₁ } = (runResult₁, finalState₁))
    (h₂ : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none)
      { s with clock := clock₂ } = (runResult₂, finalState₂))
    (hsuccess₁ : ∃ outcome, loopSemOutcomeOf runResult₁ = some outcome)
    (hsuccess₂ : ∃ outcome, loopSemOutcomeOf runResult₂ = some outcome) :
    runResult₁ = runResult₂ ∧ finalState₁.ffi.ioEvents = finalState₂.ffi.ioEvents := by
  have hnotTimeout₁ : runResult₁ ≠ some .timeOut := by
    intro htimeout
    subst runResult₁
    rcases hsuccess₁ with ⟨outcome, hOutcome⟩
    simp [loopSemOutcomeOf] at hOutcome
  have hnotTimeout₂ : runResult₂ ≠ some .timeOut := by
    intro htimeout
    subst runResult₂
    rcases hsuccess₂ with ⟨outcome, hOutcome⟩
    simp [loopSemOutcomeOf] at hOutcome
  by_cases hclock : clock₁ ≤ clock₂
  · have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
      (.call none (some start) [] none) { s with clock := clock₁ }
      runResult₁ finalState₁ (clock₂ - clock₁) h₁ hnotTimeout₁
    have hInput :
        ({ { s with clock := clock₁ } with clock := clock₁ + (clock₂ - clock₁) } :
          LoopSemStateFiniteExact width F) = { s with clock := clock₂ } := by
      cases s
      simp [Nat.add_sub_cancel' hclock]
    rw [hInput] at hLift
    have hPair :
        (runResult₁, { finalState₁ with clock := finalState₁.clock + (clock₂ - clock₁) }) =
          (runResult₂, finalState₂) := hLift.symm.trans h₂
    constructor
    · exact congrArg Prod.fst hPair
    · have hEvents := congrArg (fun p : _ × LoopSemStateFiniteExact width F => p.2.ffi.ioEvents) hPair
      simpa using hEvents
  · have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
      (.call none (some start) [] none) { s with clock := clock₂ }
      runResult₂ finalState₂ (clock₁ - clock₂) h₂ hnotTimeout₂
    have hInput :
        ({ { s with clock := clock₂ } with clock := clock₂ + (clock₁ - clock₂) } :
          LoopSemStateFiniteExact width F) = { s with clock := clock₁ } := by
      have hclock' : clock₂ ≤ clock₁ := Nat.le_of_not_ge hclock
      cases s
      simp [Nat.add_sub_cancel' hclock']
    rw [hInput] at hLift
    have hPair :
        (runResult₂, { finalState₂ with clock := finalState₂.clock + (clock₁ - clock₂) }) =
          (runResult₁, finalState₁) := hLift.symm.trans h₁
    constructor
    · exact (congrArg Prod.fst hPair).symm
    · have hEvents := congrArg (fun p : _ × LoopSemStateFiniteExact width F => p.2.ffi.ioEvents) hPair
      simpa using hEvents.symm

private theorem loopSemSuccessfulObservation_unique {width : Nat} [NeZero width] {F : Type}
    {s : LoopSemStateFiniteExact width F} {start : Nat} {result₁ result₂ : HolBehaviour}
    (h₁ : loopSemSuccessfulObservation s start result₁)
    (h₂ : loopSemSuccessfulObservation s start result₂) : result₁ = result₂ := by
  rcases h₁ with ⟨clock₁, finalState₁, runResult₁, outcome₁, hEval₁, hOutcome₁, rfl⟩
  rcases h₂ with ⟨clock₂, finalState₂, runResult₂, outcome₂, hEval₂, hOutcome₂, rfl⟩
  have hSuccess₁ : ∃ outcome, loopSemOutcomeOf runResult₁ = some outcome :=
    ⟨outcome₁, (loopSemOutcomeOf_eq_some_iff runResult₁ outcome₁).mp hOutcome₁⟩
  have hSuccess₂ : ∃ outcome, loopSemOutcomeOf runResult₂ = some outcome :=
    ⟨outcome₂, (loopSemOutcomeOf_eq_some_iff runResult₂ outcome₂).mp hOutcome₂⟩
  obtain ⟨hResult, hEvents⟩ := loopEvaluateSuccessfulObservation_unique
    s start clock₁ clock₂ runResult₁ runResult₂ finalState₁ finalState₂
    hEval₁ hEval₂ hSuccess₁ hSuccess₂
  have hOutcome : outcome₁ = outcome₂ := by
    have hEq := congrArg loopSemOutcomeOf hResult
    rw [(loopSemOutcomeOf_eq_some_iff runResult₁ outcome₁).mp hOutcome₁,
      (loopSemOutcomeOf_eq_some_iff runResult₂ outcome₂).mp hOutcome₂] at hEq
    exact Option.some.inj hEq
  simp [hOutcome, hEvents]

/-- Exact port of HOL `loop_sem_is_wrapper` (`crep_to_loopProofScript.sml:4178`):
    `loopSem$semantics s start` is the `semantics_wrapper` result of the
    clock-indexed `evaluate (Call NONE (SOME start) [] NONE, s with clock := k)`.
    The result projection maps `TimeOut` to `Incomplete`, `FinalFFI e` to
    `CompleteResult (FFI_outcome e)`, `Result _` to `CompleteResult Success`,
    and every other result to `RunError`; the state projection is exactly
    `ffi.io_events`.  The source's clock index and existential witness binders
    are retained through the exact `loopSemantics` and `evaluate` ports. Lean's
    two `holOptionSome` predicates are extensionally equivalent but have
    different syntax after mapping results; clock monotonicity makes every
    successful outcome/event observation unique, so the Lean choices coincide
    without assuming a choice-extensionality axiom. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "loop_sem_is_wrapper"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopSemIsWrapper {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat) :
    LoopSemStateFiniteExact.semantics s start =
      crepToLoopSemanticsWrapper (loopSemWrapperInput s start) := by
  classical
  have hChoice : holOptionSome (loopSemSuccessfulObservation s start) =
      holOptionSome (loopSemWrapperSuccessfulObservation s start) := by
    by_cases hex : ∃ result, loopSemSuccessfulObservation s start result
    · obtain ⟨chosen, hchosen⟩ := hex
      have hchosenWrapper := (loopSemSuccessfulObservation_iff_wrapper s start chosen).mp hchosen
      have huniq : ∀ result, loopSemSuccessfulObservation s start result → result = chosen :=
        fun result hresult => loopSemSuccessfulObservation_unique hresult hchosen
      have huniqWrapper : ∀ result, loopSemWrapperSuccessfulObservation s start result →
          result = chosen := fun result hresult =>
        loopSemSuccessfulObservation_unique
          ((loopSemSuccessfulObservation_iff_wrapper s start result).mpr hresult) hchosen
      rw [HolLList.holOptionSome_eq_some hchosen huniq,
        HolLList.holOptionSome_eq_some hchosenWrapper huniqWrapper]
    · have hnone : ∀ result, ¬ loopSemSuccessfulObservation s start result :=
        fun result hresult => hex ⟨result, hresult⟩
      have hnone₁ : holOptionSome (loopSemSuccessfulObservation s start) = none := by
        unfold holOptionSome
        have hno : ¬ ∃ result, loopSemSuccessfulObservation s start result := by
          rintro ⟨result, hresult⟩
          exact hex ⟨result, hresult⟩
        simp [hno]
      have hnone₂ : holOptionSome (loopSemWrapperSuccessfulObservation s start) = none := by
        unfold holOptionSome
        have hno : ¬ ∃ result, loopSemWrapperSuccessfulObservation s start result := by
          rintro ⟨result, hresult⟩
          exact hex ⟨result, (loopSemSuccessfulObservation_iff_wrapper s start result).mpr hresult⟩
        simp [hno]
      rw [hnone₁, hnone₂]
  unfold LoopSemStateFiniteExact.semantics crepToLoopSemanticsWrapper
  simp only [loopSemWrapperInput]
  have hFail := loopSemForbiddenRun_iff_wrapperErrorRun s start
  change
    (if ∃ clock, loopSemForbiddenResult
        (LoopSemStateFiniteExact.evaluate (.call none (some start) [] none)
          { s with clock := clock }).1 then .fail
      else match holOptionSome (loopSemSuccessfulObservation s start) with
        | some result => result
        | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
            trace = HolLList.fromList (LoopSemStateFiniteExact.evaluate
              (.call none (some start) [] none) { s with clock := clock }).2.ffi.ioEvents))) =
    (if loopSemWrapperHasErrorRun s start then .fail
      else match holOptionSome (loopSemWrapperSuccessfulObservation s start) with
        | some result => result
        | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
            trace = HolLList.fromList (loopSemWrapperInput s start clock).2)))
  rw [hFail, hChoice]
  simp [loopSemWrapperInput, Prod.map]

end Flapjack
