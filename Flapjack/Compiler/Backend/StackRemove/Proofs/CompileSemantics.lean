import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect
import Flapjack.Compiler.Backend.Semantics.StackSem.Semantics
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClockIoEventsMono

/-! Full original StackRemove compile_semantics (2418–2615), over the
faithful native evaluator and observational semantics. Local clock-family
lemmas derive termination witnesses, exclude target failure, and establish
both cofinal divergence-trace directions from actual run simulation. -/
namespace Flapjack.Compiler.Backend.StackRemove.CompileSemantics
open Flapjack Compiler.Backend.StackLang StackSemEvaluate

/-- Actual whole-entry simulation at every source clock. The compilation and
register-bound premises are discharged for the native top-level Call; target
clock/run and complete FFI equality are conclusions of full compCorrect.
This is local proof factoring, with no independent HOL declaration. -/
theorem entrySimulation {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (relation : stateRelHOL jump bounds pointer source target)
    (run : evaluate (.call none (.inl start) none, {source with clock := clock}) =
      (result, postSource))
    (nonError : result ≠ some .error) :
    ∃ extra postTarget,
      evaluate (.call none (.inl start) none, {target with clock := extra + clock}) =
        (result, postTarget) ∧ postTarget.ffi = postSource.ffi := by
  obtain ⟨extra, postTarget, targetRun, postRelation⟩ :=
    CompCorrect.Assembly.compCorrect (.call none (.inl start) none)
      {source with clock := clock} result postSource {target with clock := clock}
      pointer bounds jump ⟨run, nonError,
        RelationLaws.stateRelWithClock jump bounds pointer clock source target relation,
        by simp [StackProps.regBound]⟩
  refine ⟨extra, postTarget, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => exact (RelationLaws.stateRelConst jump bounds pointer postSource postTarget postRelation).2.2.2.2.1
    | some value =>
      cases value
      all_goals first
        | exact postRelation
        | exact (RelationLaws.stateRelConst jump bounds pointer postSource postTarget postRelation).2.2.2.2.1

/-- The original source semantics != Fail premise excludes an Error run at
any clock. This unfolds the actual fail guard, with no source safety premise
added to the final observational theorem. Local Flapjack proof factoring. -/
theorem sourceRunNonError {width : Nat} [NeZero width] {C F : Type}
    (start clock : Nat) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (notFail : semantics start source ≠ HolBehaviour.fail)
    (run : evaluate (.call none (.inl start) none, {source with clock := clock}) =
      (result, post)) : result ≠ some .error := by
  intro isError
  have bad : ∃ k,
      let res := (evaluate (.call none (.inl start) none, {source with clock := k})).1
      res ≠ some .timeOut ∧ res ≠ some (.result (.loc 1 0)) ∧
      (∀ w, res ≠ some (.halt (.word w))) ∧ ∀ e, res ≠ some (.finalFFI e) := by
    refine ⟨clock, ?_⟩
    simp only [run, isError]
    simp
  exact notFail (by simp only [semantics, bad, if_true])

/-- Native entry simulation derived from exactly the original observational
premises. Non-Error follows from source semantics rather than a new assumption.
Local Flapjack proof factoring, not the full compile_semantics theorem. -/
theorem entrySimulationOfNotFail {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (relation : stateRelHOL jump bounds pointer source target)
    (notFail : semantics start source ≠ HolBehaviour.fail)
    (run : evaluate (.call none (.inl start) none, {source with clock := clock}) =
      (result, postSource)) :
    ∃ extra postTarget,
      evaluate (.call none (.inl start) none, {target with clock := extra + clock}) =
        (result, postTarget) ∧ postTarget.ffi = postSource.ffi :=
  entrySimulation jump bounds pointer start clock source target postSource result
    relation run (sourceRunNonError start clock source postSource result notFail run)

/-- Every native evaluator clock family is prefix-monotone. This instantiates
the accepted unconditional extra-clock theorem; no desired trace law is assumed.
Local Flapjack proof factoring for the original divergence-chain argument. -/
theorem clockFamilyEventsPrefix {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (lower upper : Nat) (ordered : lower ≤ upper) :
    (evaluate (program, {source with clock := lower})).2.ffi.ioEvents <+:
      (evaluate (program, {source with clock := upper})).2.ffi.ioEvents := by
  have eventsPrefix := StackProps.EvaluateAddClockIoEventsMono.evaluateAddClockIoEventsMono
    (upper - lower) program {source with clock := lower}
  simpa only [Nat.add_sub_of_le ordered] using eventsPrefix

/-- Exact clock-indexed event family used by the native semantics definition.
Local naming for proof factoring; no independent HOL declaration. -/
def clockEventFamily {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (trace : HolLList HolIoEvent) : Prop :=
  ∃ clock, trace = HolLList.fromList
    (evaluate (program, {source with clock := clock})).2.ffi.ioEvents

/-- Native clock families form lazy-list prefix chains by the accepted actual
extra-clock theorem. Local proof factoring, no assumed event-prefix law. -/
theorem clockEventFamilyChain {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F) :
    HolLList.lprefixChain (clockEventFamily program source) := by
  rintro first second ⟨firstClock, rfl⟩ ⟨secondClock, rfl⟩
  rcases Nat.le_total firstClock secondClock with ordered | ordered
  · exact Or.inl ((HolLList.lprefix_fromList _ _).mpr
      (clockFamilyEventsPrefix program source firstClock secondClock ordered))
  · exact Or.inr ((HolLList.lprefix_fromList _ _).mpr
      (clockFamilyEventsPrefix program source secondClock firstClock ordered))

/-- Full native divergence-family equality from exactly the original relation
and non-Fail premise. Both cofinal prefix directions are proved using actual
entry simulations and evaluator monotonicity, never supplied as hypotheses.
Local proof factoring for the original compile_semantics divergence clause. -/
theorem entryEventLubEquality {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (notFail : semantics start source ≠ HolBehaviour.fail) :
    HolLList.buildLprefixLub (clockEventFamily (.call none (.inl start) none) source) =
      HolLList.buildLprefixLub (clockEventFamily (.call none (.inl start) none) target) := by
  apply HolLList.IMP_build_lprefix_lub_EQ
    (clockEventFamilyChain _ source) (clockEventFamilyChain _ target)
  · rintro trace ⟨clock, rfl⟩
    rcases run : evaluate (.call none (.inl start) none, {source with clock := clock}) with ⟨result, postSource⟩
    obtain ⟨extra, postTarget, targetRun, ffi⟩ :=
      entrySimulationOfNotFail jump bounds pointer start clock source target postSource result relation notFail run
    refine ⟨HolLList.fromList postTarget.ffi.ioEvents, ⟨extra + clock, ?_⟩, ?_⟩
    · rw [targetRun]
    · rw [ffi]
      exact (HolLList.lprefix_fromList _ _).mpr (List.prefix_refl _)
  · rintro trace ⟨clock, rfl⟩
    rcases run : evaluate (.call none (.inl start) none, {source with clock := clock}) with ⟨result, postSource⟩
    obtain ⟨extra, postTarget, targetRun, ffi⟩ :=
      entrySimulationOfNotFail jump bounds pointer start clock source target postSource result relation notFail run
    refine ⟨HolLList.fromList postSource.ffi.ioEvents, ⟨clock, ?_⟩, ?_⟩
    · rw [run]
    · apply (HolLList.lprefix_fromList _ _).mpr
      have eventsPrefix := clockFamilyEventsPrefix (.call none (.inl start) none) target
        clock (extra + clock) (by omega)
      simpa only [targetRun, ffi] using eventsPrefix

/-- A non-timeout target run agrees with the source run at the same clock.
Both actual runs are local comparison premises; the final observational theorem
must derive its witnesses rather than assume a target execution. -/
theorem entryRunAgreement {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource postTarget : StackSemStateFiniteExact width C F)
    (sourceResult targetResult : Option (StackSemResult width))
    (relation : stateRelHOL jump bounds pointer source target)
    (notFail : semantics start source ≠ HolBehaviour.fail)
    (sourceRun : evaluate (.call none (.inl start) none, {source with clock := clock}) =
      (sourceResult, postSource))
    (targetRun : evaluate (.call none (.inl start) none, {target with clock := clock}) =
      (targetResult, postTarget))
    (nonTimeout : targetResult ≠ some .timeOut) :
    targetResult = sourceResult ∧ postTarget.ffi = postSource.ffi := by
  obtain ⟨extra, compiledPost, compiledRun, ffi⟩ :=
    entrySimulationOfNotFail jump bounds pointer start clock source target postSource sourceResult
      relation notFail sourceRun
  have boostedRun := StackProps.evaluateAddClock extra (.call none (.inl start) none)
    {target with clock := clock} targetResult postTarget ⟨targetRun, nonTimeout⟩
  have same : (targetResult, {postTarget with clock := postTarget.clock + extra}) =
      (sourceResult, compiledPost) := by
    rw [← boostedRun]
    simpa only [Nat.add_comm] using compiledRun
  rcases Prod.mk.inj same with ⟨resultEqual, postEqual⟩
  refine ⟨resultEqual, ?_⟩
  have ffiEqual := congrArg StackSemStateFiniteExact.ffi postEqual
  exact ffiEqual.trans ffi

/-- Local name for the actual native semantics fail guard. -/
def badResult {width : Nat} [NeZero width] (result : Option (StackSemResult width)) : Prop :=
  result ≠ some .timeOut ∧ result ≠ some (.result (.loc 1 0)) ∧
    (∀ w, result ≠ some (.halt (.word w))) ∧ ∀ e, result ≠ some (.finalFFI e)

/-- Local clock witness of the original fail branch, not an alternate semantics. -/
def badEntry {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∃ clock, badResult (evaluate (.call none (.inl start) none, {source with clock := clock})).1

/-- The original observational premise rules out exactly the native fail guard. -/
theorem sourceNoBadEntry {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (source : StackSemStateFiniteExact width C F)
    (notFail : semantics start source ≠ HolBehaviour.fail) : ¬badEntry start source := by
  intro bad
  apply notFail
  have guard := bad
  unfold badEntry badResult at guard
  simp only [semantics, guard, if_true]

/-- Every target fail witness would be a same-clock source fail witness,
by actual non-timeout run agreement. No target safety is assumed. -/
theorem targetNoBadEntry {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (notFail : semantics start source ≠ HolBehaviour.fail) : ¬badEntry start target := by
  rintro ⟨clock, bad⟩
  rcases targetRun : evaluate (.call none (.inl start) none, {target with clock := clock}) with ⟨targetResult, postTarget⟩
  rw [targetRun] at bad
  rcases sourceRun : evaluate (.call none (.inl start) none, {source with clock := clock}) with ⟨sourceResult, postSource⟩
  have agreement := entryRunAgreement jump bounds pointer start clock source target postSource postTarget
    sourceResult targetResult relation notFail sourceRun targetRun bad.1
  apply sourceNoBadEntry start source notFail
  refine ⟨clock, ?_⟩
  rw [sourceRun, ←agreement.1]
  exact bad

/-- Local name for the exact native `some` termination-choice predicate. -/
def terminationWitness {width : Nat} [NeZero width] {C F : Type}
    (start : Nat) (source : StackSemStateFiniteExact width C F) (behaviour : HolBehaviour) : Prop :=
  ∃ clock post result outcome,
    evaluate (.call none (.inl start) none, {source with clock := clock}) = (some result, post) ∧
    (match result with
     | .finalFFI e => outcome = HolOutcome.ffiOutcome e
     | .halt value => outcome = if value = .word 0 then HolOutcome.success else HolOutcome.resourceLimitHit
     | .result _ => outcome = HolOutcome.success
     | _ => False) ∧
    behaviour = HolBehaviour.terminate outcome post.ffi.ioEvents

/-- Complete equality of the native termination-choice predicates. Source
runs produce actual target witnesses; target witnesses agree with the actual
source run at the same clock. Neither direction assumes an output trace. -/
theorem terminationWitnessIff {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (notFail : semantics start source ≠ HolBehaviour.fail) (behaviour : HolBehaviour) :
    terminationWitness start source behaviour ↔ terminationWitness start target behaviour := by
  constructor
  · rintro ⟨clock, postSource, result, outcome, run, outcomeEq, behaviourEq⟩
    obtain ⟨extra, postTarget, targetRun, ffi⟩ :=
      entrySimulationOfNotFail jump bounds pointer start clock source target postSource (some result)
        relation notFail run
    refine ⟨extra + clock, postTarget, result, outcome, targetRun, outcomeEq, ?_⟩
    simpa only [ffi] using behaviourEq
  · rintro ⟨clock, postTarget, result, outcome, targetRun, outcomeEq, behaviourEq⟩
    have nonTimeout : some result ≠ some (.timeOut : StackSemResult width) := by
      cases result <;> simp_all
    rcases sourceRun : evaluate (.call none (.inl start) none, {source with clock := clock}) with ⟨sourceResult, postSource⟩
    have agreement := entryRunAgreement jump bounds pointer start clock source target postSource postTarget
      sourceResult (some result) relation notFail sourceRun targetRun nonTimeout
    refine ⟨clock, postSource, result, outcome, ?_, outcomeEq, ?_⟩
    · simpa only [←agreement.1] using sourceRun
    · simpa only [agreement.2] using behaviourEq

/-- Canonical codec of the actual imported native evaluator state owner. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original `compile_semantics` (2418–2615). Exactly the original
state relation and source non-Fail premises; target failure exclusion,
termination-choice equality and divergence trace equality are proved.
Every run simulation and clock/trace property is derived from the accepted
native compCorrect and evaluator theorems. The native evaluator closure
inherits reviewed reals_as_rational_cuts (SOUNDNESS item 8); this theorem
does not assert numerical FP parity or whole compiler correctness. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "compile_semantics"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compileSemantics {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      semantics start source ≠ HolBehaviour.fail) :
    semantics start target = semantics start source := by
  classical
  have sourceSafe := sourceNoBadEntry start source hypothesis.2
  have targetSafe := targetNoBadEntry jump bounds pointer start source target hypothesis.1 hypothesis.2
  have predicates : terminationWitness start target = terminationWitness start source := by
    funext behaviour
    exact propext (terminationWitnessIff jump bounds pointer start source target
      hypothesis.1 hypothesis.2 behaviour).symm
  change (if badEntry start target then .fail else
    match holOptionSome (terminationWitness start target) with
    | some result => result
    | none => .diverge (HolLList.buildLprefixLub (clockEventFamily (.call none (.inl start) none) target))) =
    (if badEntry start source then .fail else
    match holOptionSome (terminationWitness start source) with
    | some result => result
    | none => .diverge (HolLList.buildLprefixLub (clockEventFamily (.call none (.inl start) none) source)))
  rw [if_neg targetSafe, if_neg sourceSafe, predicates]
  cases holOptionSome (terminationWitness start source) with
  | some result => rfl
  | none =>
    dsimp only
    congr 1
    exact (entryEventLubEquality jump bounds pointer start source target hypothesis.1 hypothesis.2).symm

end Flapjack.Compiler.Backend.StackRemove.CompileSemantics
