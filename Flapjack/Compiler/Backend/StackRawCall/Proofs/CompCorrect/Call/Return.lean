import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Tail

namespace Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase RawCallCase

/-- Synchronized register erasure preserves the literal relation. Flapjack
infrastructure, with code and entry-frame witnesses unchanged. -/
theorem stateRel_eraseRegs {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (link : Nat) :
    stateRel info {source with regs := source.regs.eraseEq link}
      {target with regs := target.regs.eraseEq link} := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

/-- The actual returning-call lookup erases the link register before resolving
either destination form. The entry relation is recovered on the original
states, without an assumption about the eventual target run. -/
theorem callEntryErased {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (dest : Sum Nat Nat) (link : Nat)
    (program : HolProg width)
    (lookup : findCode dest (source.regs.eraseEq link) source.code = some program) :
    ∃ entryInfo : Spt Nat, stateRel entryInfo source target ∧
      findCode dest (target.regs.eraseEq link) target.code = some (compTop entryInfo program) := by
  obtain ⟨entryInfo, erasedRelation, targetLookup⟩ :=
    callEntry info {source with regs := source.regs.eraseEq link}
      {target with regs := target.regs.eraseEq link}
      (stateRel_eraseRegs info source target relation link) dest program lookup
  have entryFrames : stateOk entryInfo source.code := by
    obtain ⟨_, _, _, frames, _⟩ := erasedRelation
    exact frames
  exact ⟨entryInfo, stateRel_changeInfo info entryInfo source target relation entryFrames,
    targetLookup⟩

/-- Synchronized return-link update preserves the literal relation. Flapjack
infrastructure over the actual canonical register maps. -/
theorem stateRel_setVar {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (link : Nat) (value : WordLocW width) :
    stateRel info (setVar link value source) (setVar link value target) := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

/-- Native returning-call input commutes with an added allowance when its
original clock is nonzero. Flapjack infrastructure, no execution premise. -/
theorem returningInput_addClock {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (link l1 l2 extra : Nat)
    (nonzero : target.clock ≠ 0) :
    decClock (setVar link (.loc l1 l2) {target with clock := target.clock + extra}) =
      {decClock (setVar link (.loc l1 l2) target) with
        clock := (decClock (setVar link (.loc l1 l2) target)).clock + extra} := by
  simp only [decClock, setVar]
  congr 1
  omega

/-- The actual SOME-return callee IH at the fixed recursive source; unused comp
component omitted. Flapjack notation for the original evaluate_ind motive. -/
abbrev ReturnCalleeIH {width : Nat} [NeZero width] (C F : Type)
    (dest : Sum Nat Nat) (link l1 l2 : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 →
    ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
      (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (result, post) ∧ result ≠ some .error ∧
        stateRel info (decClock (setVar link (.loc l1 l2) source)) target →
      SimulationResult (compTop info program) info target post result

/-- Original return-continuation IH, guarded by the real callee lookup, clock,
evaluation and exact matching return location. Flapjack infrastructure. -/
abbrev ReturnContinuationIH {width : Nat} [NeZero width] (C F : Type)
    (ret : HolProg width) (dest : Sum Nat Nat) (link l1 l2 : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 → ∀ middle,
    StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.result (.loc l1 l2)), middle) → ProgramIH C F ret middle

/-- Original exception-continuation IH, retaining the actual handler and exact
matching exception location guards. Flapjack infrastructure. -/
abbrev ExceptionContinuationIH {width : Nat} [NeZero width] (C F : Type)
    (handler : Option (HolProg width × Nat × Nat)) (dest : Sum Nat Nat)
    (link l1 l2 : Nat) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ program h hl1 hl2,
    findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 → handler = some (h, hl1, hl2) → ∀ middle,
    StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.exception (.loc hl1 hl2)), middle) → ProgramIH C F h middle

/-- Derive the actual compiled callee execution and restore the outer frame
information from code monotonicity. Flapjack source-local infrastructure. -/
theorem simulateReturningCallee {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (link l1 l2 : Nat) (info : Spt Nat)
    (source target middle : StackSemStateFiniteExact width C F)
    (program : HolProg width) (result : Option (StackSemResult width))
    (calleeIH : ReturnCalleeIH C F dest link l1 l2 source)
    (relation : stateRel info source target)
    (lookup : findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate
      (program, decClock (setVar link (.loc l1 l2) source)) = (result, middle))
    (nonerror : result ≠ some .error) :
    ∃ entryInfo, findCode dest (target.regs.eraseEq link) target.code =
        some (compTop entryInfo program) ∧
      SimulationResult (compTop entryInfo program) info
        (decClock (setVar link (.loc l1 l2) target)) middle result := by
  obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
    callEntryErased info source target relation dest link program lookup
  obtain ⟨clock, targetMiddle, space, middleRelation, targetExecution, guard⟩ :=
    calleeIH program lookup nonzero entryInfo
      (decClock (setVar link (.loc l1 l2) target)) middle result
      ⟨execution, nonerror, LoopCase.stateRel_decClock entryInfo
        (setVar link (.loc l1 l2) source) (setVar link (.loc l1 l2) target)
        (stateRel_setVar entryInfo source target entryRelation link (.loc l1 l2))⟩
  have frames : stateOk info source.code := by
    obtain ⟨_, _, _, frames, _⟩ := relation
    exact frames
  have middleFrames := stateOk_afterEvaluate info program
    (decClock (setVar link (.loc l1 l2) source)) middle result frames execution
  exact ⟨entryInfo, targetLookup, clock, targetMiddle, space,
    stateRel_changeInfo entryInfo info middle targetMiddle middleRelation middleFrames,
    targetExecution, guard⟩

/-- Extending a derived returning-callee run composes both allowances at the
real native call input. Flapjack clock infrastructure, not a ported case. -/
theorem extendReturningCallee {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (target middle : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (link l1 l2 first extra : Nat)
    (nonzero : target.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate
      (program, {decClock (setVar link (.loc l1 l2) target) with
        clock := (decClock (setVar link (.loc l1 l2) target)).clock + first}) =
      (result, middle)) (nonTimeout : result ≠ some .timeOut) :
    StackSemEvaluate.evaluate
      (program, decClock (setVar link (.loc l1 l2)
        {target with clock := target.clock + (first + extra)})) =
      (result, {middle with clock := middle.clock + extra}) := by
  have extended := Compiler.Backend.StackProps.evaluateAddClock extra program
    {decClock (setVar link (.loc l1 l2) target) with
      clock := (decClock (setVar link (.loc l1 l2) target)).clock + first}
    result middle ⟨execution, nonTimeout⟩
  rw [returningInput_addClock target link l1 l2 (first + extra) nonzero]
  simpa only [Nat.add_assoc] using extended


namespace ReturnRepresentation
/-- Actual imported canonical evaluator-state roundtrip. Flapjack qualifier
infrastructure without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness
end ReturnRepresentation

/-- Genuine SOME-return Call branch409-518. The original three source premises
and exactly guarded callee, return and exception induction hypotheses establish
both existential simulations. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCallReturn {width : Nat} [NeZero width] {C F : Type}
    (ret : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : ReturnCalleeIH C F dest link l1 l2 source)
    (returnIH : ReturnContinuationIH C F ret dest link l1 l2 source)
    (exceptionIH : ExceptionContinuationIH C F handler dest link l1 l2 source)
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result ∧
    SimulationResult (comp info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result := by
  classical
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  suffices simulation :
      SimulationResult (comp info (.call (some (ret, link, l1, l2)) dest handler))
        info target post result by
    exact ⟨by simpa only [compTop] using simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_call] at execution
  dsimp only at execution
  cases lookup : findCode dest (source.regs.eraseEq link) source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      have clockEq := LoopCase.stateRel_clock info source target relation
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨entryInfo, _, targetLookup⟩ :=
          callEntryErased info source target relation dest link program lookup
        refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
          LoopCase.stateRel_emptyEnv info source target relation, ?_, by simp⟩
        have targetZero : target.clock = 0 := clockEq.trans zero
        have update : {target with clock := 0} = target := by rw [← targetZero]
        cases handler with
        | none =>
            simp only [comp, Nat.add_zero, targetZero, update,
              StackSemEvaluate.evaluate_call, targetLookup, if_true]
        | some triple =>
            obtain ⟨h, hl1, hl2⟩ := triple
            simp only [comp, Nat.add_zero, targetZero, update,
              StackSemEvaluate.evaluate_call, targetLookup, if_true]
      · simp only [zero, if_false] at execution
        rw [StackSemEvaluateClock.fixClockEvaluate] at execution
        rcases bodyExecution : StackSemEvaluate.evaluate
          (program, decClock (setVar link (.loc l1 l2) source)) with
          ⟨bodyResult, middle⟩
        rw [bodyExecution] at execution
        have bodyNonerror : bodyResult ≠ some .error := by
          intro equal
          rw [equal] at execution
          simp only [Prod.mk.injEq] at execution
          exact nonerror execution.1.symm
        obtain ⟨entryInfo, targetLookup, firstClock, targetMiddle, firstSpace,
          middleRelation, calleeExecution, firstGuard⟩ :=
          simulateReturningCallee dest link l1 l2 info source target middle program bodyResult
            calleeIH relation lookup zero bodyExecution bodyNonerror
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + firstClock ≠ 0 := by omega
        have calleeNative : StackSemEvaluate.evaluate
            (compTop entryInfo program, decClock (setVar link (.loc l1 l2)
              {target with clock := target.clock + firstClock})) =
            (bodyResult, {targetMiddle with stackSpace := firstSpace}) := by
          rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
          exact calleeExecution
        cases bodyResult with
        | none =>
            simp only [Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
        | some value =>
            cases value with
            | error => exact False.elim (bodyNonerror rfl)
            | «break» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | «continue» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | halt value =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard⟩
                cases handler with
                | none =>
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
            | timeOut =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard⟩
                cases handler with
                | none =>
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
            | finalFFI event =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard⟩
                cases handler with
                | none =>
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
            | result value =>
                by_cases equal : value = .loc l1 l2
                · subst value
                  simp only [ne_eq, not_true_eq_false, if_false] at execution
                  have spaceEq := firstGuard (by simp)
                  subst firstSpace
                  have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                      targetMiddle := by cases targetMiddle; rfl
                  rw [selfSpace] at calleeExecution
                  obtain ⟨secondClock, targetPost, finalSpace, postRelation,
                    continuationExecution, finalGuard⟩ :=
                    returnIH program lookup zero middle bodyExecution info targetMiddle post result
                      ⟨execution, nonerror, middleRelation⟩
                  have extended := extendReturningCallee (compTop entryInfo program) target
                    targetMiddle (some (.result (.loc l1 l2))) link l1 l2 firstClock secondClock
                    targetNonzero calleeExecution (by simp)
                  have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                  refine ⟨firstClock + secondClock, targetPost, finalSpace, postRelation, ?_, finalGuard⟩
                  cases handler with
                  | none =>
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        totalNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                      simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        totalNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                      simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                  exact False.elim (nonerror execution.1.symm)
            | exception value =>
                cases handler with
                | none =>
                    simp only [Prod.mk.injEq] at execution
                    obtain ⟨rfl, rfl⟩ := execution
                    refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard⟩
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                      addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    by_cases equal : value = .loc hl1 hl2
                    · subst value
                      simp only [ne_eq, not_true_eq_false, if_false] at execution
                      have spaceEq := firstGuard (by simp)
                      subst firstSpace
                      have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                          targetMiddle := by cases targetMiddle; rfl
                      rw [selfSpace] at calleeExecution
                      obtain ⟨secondClock, targetPost, finalSpace, postRelation,
                        continuationExecution, finalGuard⟩ :=
                        exceptionIH program h hl1 hl2 lookup zero rfl middle bodyExecution
                          info targetMiddle post result ⟨execution, nonerror, middleRelation⟩
                      have extended := extendReturningCallee (compTop entryInfo program) target
                        targetMiddle (some (.exception (.loc hl1 hl2))) link l1 l2
                        firstClock secondClock targetNonzero calleeExecution (by simp)
                      have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                      refine ⟨firstClock + secondClock, targetPost, finalSpace,
                        postRelation, ?_, finalGuard⟩
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        totalNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                      simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                    · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                      exact False.elim (nonerror execution.1.symm)

end Flapjack.Compiler.Backend.StackRawCall.CallCase
