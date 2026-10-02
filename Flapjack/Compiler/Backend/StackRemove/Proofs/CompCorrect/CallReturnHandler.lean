import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallReturnNone
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps
open CallReturnNone

/-- Flapjack proof infrastructure for the original returning Call case.
This removes the native clock clamp using the unconditional evaluator theorem;
it claims no independent HOL declaration. Every original result branch remains. -/
theorem evaluateCallReturnHandlerUnclamped {width : Nat} [NeZero width] {C F : Type}
    (body handler : HolProg width) (link l1 l2 hl1 hl2 : Nat) (dest : Sum Nat Nat)
    (source : StackSemStateFiniteExact width C F) :
    evaluate (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) =
      match StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
      | none => (some .error, source)
      | some program =>
        if source.clock = 0 then (some .timeOut, emptyEnv source)
        else
          match evaluate (program, decClock (setVar link (.loc l1 l2) source)) with
          | (some (.result value), middle) =>
            if value ≠ .loc l1 l2 then (some .error, middle)
            else evaluate (body, middle)
          | (some (.exception value), middle) =>
            if value ≠ .loc hl1 hl2 then (some .error, middle)
            else evaluate (handler, middle)
          | (none, middle) => (some .error, middle)
          | (some (.break _), middle) => (some .error, middle)
          | (some (.continue _), middle) => (some .error, middle)
          | (result, middle) => (result, middle) := by
  rw [evaluate_call]
  cases lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none => simp only [lookup]
  | some program =>
    simp only [lookup]
    split
    · rfl
    · rw [StackSemEvaluateClock.fixClockEvaluate]
      rfl

/-- Flapjack proof infrastructure for composing the callee and exception-body
clock allowances. The run is the intermediate conclusion obtained from the
callee IH, not a premise of a tagged pass-correctness port. The actual exception
result discharges the non-TimeOut condition of `evaluateAddClock`. -/
theorem exceptionAllowance {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (target post : StackSemStateFiniteExact width C F)
    (link l1 l2 hl1 hl2 first second : Nat) (nonzero : target.clock ≠ 0)
    (run : evaluate (program,
      {decClock (setVar link (.loc l1 l2) target) with
        clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) =
      (some (.exception (.loc hl1 hl2)), post)) :
    evaluate (program,
      decClock (setVar link (.loc l1 l2)
        {target with clock := (first + second) + target.clock})) =
      (some (.exception (.loc hl1 hl2)), {post with clock := second + post.clock}) := by
  rw [entryClock target link l1 l2 (first + second) nonzero]
  have boosted := StackProps.evaluateAddClock second program
    {decClock (setVar link (.loc l1 l2) target) with
      clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}
    (some (.exception (.loc hl1 hl2))) post ⟨run, by simp⟩
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using boosted

/-- Source-local actual successful-return branch equation, used for both
source and compiled target. This has no separate HOL declaration. -/
theorem evaluateCallReturnHandlerResult {width : Nat} [NeZero width] {C F : Type}
    (body handler program : HolProg width) (link l1 l2 hl1 hl2 : Nat) (dest : Sum Nat Nat)
    (source middle : StackSemStateFiniteExact width C F)
    (lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (run : evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.result (.loc l1 l2)), middle)) :
    evaluate (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) =
      evaluate (body, middle) := by
  rw [evaluateCallReturnHandlerUnclamped]
  simp only [lookup, nonzero, if_false, run, ne_eq, not_true_eq_false]

/-- Source-local actual successful-exception branch equation, used for both
source and compiled target. This has no separate HOL declaration. -/
theorem evaluateCallReturnHandlerException {width : Nat} [NeZero width] {C F : Type}
    (body handler program : HolProg width) (link l1 l2 hl1 hl2 : Nat) (dest : Sum Nat Nat)
    (source middle : StackSemStateFiniteExact width C F)
    (lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (run : evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.exception (.loc hl1 hl2)), middle)) :
    evaluate (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) =
      evaluate (handler, middle) := by
  rw [evaluateCallReturnHandlerUnclamped]
  simp only [lookup, nonzero, if_false, run, ne_eq, not_true_eq_false]

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Original returning Call with handler SOME, retaining every source result.
Only actual source lookup/nonzero-clock guarded callee and actual successful
return-location and exception-location guarded continuations induction hypotheses are added to the
original four premises. Intermediate target runs and relations are derived. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectCallReturnHandler {width : Nat} [NeZero width] {C F : Type}
    (body handler : HolProg width) (link l1 l2 hl1 hl2 : Nat) (dest : Sum Nat Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (program : HolProg width),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock (setVar link (.loc l1 l2) source)) t ∧ StackProps.regBound program k →
      ∃ clock postTarget,
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (returnIH : ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (some (.result (.loc l1 l2)), middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (middle) t ∧ StackProps.regBound body k →
      ∃ clock postTarget,
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (handlerIH : ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (some (.exception (.loc hl1 hl2)), middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (handler, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (middle) t ∧ StackProps.regBound handler k →
      ∃ clock postTarget,
        evaluate (comp j off k handler, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) =
        (result, postSource) ∧ result ≠ some .error ∧
      stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2))) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2))),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluateCallReturnHandlerUnclamped] at sourceRun
  cases lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    obtain ⟨targetLookup, programBound⟩ := FindCode.findCodeLemmaErased jump bounds pointer
      source target dest program link ⟨relation, by
        simp only [StackProps.regBound] at bound
        cases dest <;> exact bound.1, lookup⟩
    have bodyBound : StackProps.regBound body pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.1
    have linkBound : link < pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.2.1
    have handlerBound : StackProps.regBound handler pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.2.2
    by_cases zero : source.clock = 0
    · simp only [zero, if_true] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
      subst result
      subst postSource
      refine ⟨0, emptyEnv target, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluateCallReturnHandlerUnclamped (comp jump bounds pointer body)
            (comp jump bounds pointer handler) link l1 l2 hl1 hl2 dest target).trans (by
            simp only [targetLookup, clocks, zero, if_true])
      · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
    · simp only [zero, if_false] at sourceRun
      have targetNonzero : target.clock ≠ 0 := by omega
      have entry := entryRelation jump bounds pointer link l1 l2 source target relation linkBound
      rcases bodyRun : evaluate (program, decClock (setVar link (.loc l1 l2) source)) with
        ⟨bodyResult, middle⟩
      rw [bodyRun] at sourceRun
      cases bodyResult with
      | none =>
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some value =>
        cases value with
        | error => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «break» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «continue» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | result value =>
          change (if value ≠ .loc l1 l2 then (some .error, middle)
            else evaluate (body, middle)) = (result, postSource) at sourceRun
          split at sourceRun
          · exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          · rename_i equal
            have correct : value = .loc l1 l2 := by simpa only [ne_eq, not_not] using equal
            subst value
            obtain ⟨first, middleTarget, calleeRun, middleRelation⟩ :=
              calleeIH program lookup zero (some (.result (.loc l1 l2))) middle
                (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
                ⟨bodyRun, by simp, entry, programBound⟩
            obtain ⟨second, postTarget, returnRun, postRelation⟩ :=
              returnIH program middle lookup zero bodyRun result postSource middleTarget pointer bounds jump
                ⟨sourceRun, notError, middleRelation, bodyBound⟩
            have boosted := calleeAllowance (comp jump bounds pointer program) target middleTarget
              link l1 l2 first second targetNonzero calleeRun
            refine ⟨first + second, postTarget, ?_, ?_⟩
            · have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
              simp only [comp]
              rw [evaluateCallReturnHandlerResult (comp jump bounds pointer body)
                (comp jump bounds pointer handler) (comp jump bounds pointer program) link l1 l2 hl1 hl2 dest
                {target with clock := (first + second) + target.clock}
                {middleTarget with clock := second + middleTarget.clock}
                targetLookup totalNonzero boosted]
              exact returnRun
            · cases result with
              | none => exact postRelation
              | some r => cases r <;> exact postRelation
        | halt n =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.halt n)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnHandlerUnclamped]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClock target link l1 l2 clock targetNonzero, targetRun]
        | timeOut =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.timeOut)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnHandlerUnclamped]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClock target link l1 l2 clock targetNonzero, targetRun]
        | finalFFI event =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.finalFFI event)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnHandlerUnclamped]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClock target link l1 l2 clock targetNonzero, targetRun]
        | exception value =>
          change (if value ≠ .loc hl1 hl2 then (some .error, middle)
            else evaluate (handler, middle)) = (result, postSource) at sourceRun
          split at sourceRun
          · exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          · rename_i equal
            have correct : value = .loc hl1 hl2 := by simpa only [ne_eq, not_not] using equal
            subst value
            obtain ⟨first, middleTarget, calleeRun, middleRelation⟩ :=
              calleeIH program lookup zero (some (.exception (.loc hl1 hl2))) middle
                (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
                ⟨bodyRun, by simp, entry, programBound⟩
            obtain ⟨second, postTarget, returnRun, postRelation⟩ :=
              handlerIH program middle lookup zero bodyRun result postSource middleTarget pointer bounds jump
                ⟨sourceRun, notError, middleRelation, handlerBound⟩
            have boosted := exceptionAllowance (comp jump bounds pointer program) target middleTarget
              link l1 l2 hl1 hl2 first second targetNonzero calleeRun
            refine ⟨first + second, postTarget, ?_, ?_⟩
            · have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
              simp only [comp]
              rw [evaluateCallReturnHandlerException (comp jump bounds pointer body)
                (comp jump bounds pointer handler) (comp jump bounds pointer program) link l1 l2 hl1 hl2 dest
                {target with clock := (first + second) + target.clock}
                {middleTarget with clock := second + middleTarget.clock}
                targetLookup totalNonzero boosted]
              exact returnRun
            · cases result with
              | none => exact postRelation
              | some r => cases r <;> exact postRelation

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler
