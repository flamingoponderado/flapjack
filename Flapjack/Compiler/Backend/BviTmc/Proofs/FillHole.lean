import Flapjack.Compiler.Backend.BviTmc.Proofs.EvaluateRewrite
import Flapjack.Compiler.Backend.BviTailrec.Proofs.PrimitiveRelation

/-! Evaluation of the TMC hole-filling operation. -/
namespace Flapjack.Compiler.Backend.BviTmc.FillHole
open BviTmc BviSem BvlSem ResultRelation SemanticPrimitivesProps

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- Flapjack infrastructure: filling an unfinalised mutable block writes the
evaluated value into the indicated slot and returns unit. -/
theorem evaluate_fillHole_update {C F : Type} (e : Bvi.Exp) (ptrIndex idxIndex ptr tag : Nat)
    (left : List Value) (oldChild : Value) (right : List Value) (env : List Value)
    (state next : BviState C F) (value : Value)
    (run : evaluate [e] env state = (.val [value], next))
    (ptrAt : env[ptrIndex]? = some (.refPtr false ptr))
    (idxAt : env[idxIndex]? = some (.number (Int.ofNat left.length)))
    (found : next.refs.lookup ptr = some (.mutBlock tag false left oldChild right)) :
    evaluate [fillHoleSource ptrIndex idxIndex e] env state =
      (.val [unitValue], { next with refs := next.refs.updateEq (ptr, .mutBlock tag false left value right) }) := by
  have operands : evaluate [e, .var idxIndex, .var ptrIndex] env state =
      (.val [value, .number (Int.ofNat left.length), .refPtr false ptr], next) := by
    have idxRun : evaluate [.var idxIndex] env next = (.val [.number (Int.ofNat left.length)], next) := by
      simp [BviSem.evaluate, idxAt]
    have ptrRun : evaluate [.var ptrIndex] env next = (.val [.refPtr false ptr], next) := by
      simp [BviSem.evaluate, ptrAt]
    have restRun : evaluate [.var idxIndex, .var ptrIndex] env next =
        (.val [.number (Int.ofNat left.length), .refPtr false ptr], next) := by
      change evaluateTuple (.var idxIndex :: [.var ptrIndex], env, next) = _
      rw [evaluateCons]
      simp [BviSem.evaluateTuple, idxRun, ptrRun, Flapjack.holHd]
    change evaluateTuple (e :: [.var idxIndex, .var ptrIndex], env, state) = _
    rw [evaluateCons]
    simp [BviSem.evaluateTuple, run, restRun, Flapjack.holHd]
  simp only [fillHoleSource, updateConsSource]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, operands]
  simp [BviTailrec.doApp_updateCons_effect, BviTailrec.updateConsEffect, found]

/-- Flapjack infrastructure: an error in the value expression propagates
without evaluating the pointer or index expressions. -/
theorem evaluate_fillHole_error {C F : Type} (e : Bvi.Exp) (ptrIndex idxIndex : Nat)
    (env : List Value) (state next : BviState C F) (error : SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (run : evaluate [e] env state = (.err error, next)) :
    evaluate [fillHoleSource ptrIndex idxIndex e] env state = (.err error, next) := by
  have operands : evaluate [e, .var idxIndex, .var ptrIndex] env state = (.err error, next) := by
    change evaluateTuple (e :: [.var idxIndex, .var ptrIndex], env, state) = _
    rw [evaluateCons]
    simp [BviSem.evaluateTuple, run]
  simp only [fillHoleSource, updateConsSource]
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, operands]

/-- Flapjack infrastructure: ordinary related values form a trivial mutable
block relation, independently of the heap. -/
theorem mutableBlockRel_of_valueRel (f : HolFiniteMapExact Nat Nat)
    (old : HolFiniteMapExact Nat (Ref Value)) (refs : HolFiniteMapExact Nat (Ref Value))
    (source target : Value) (related : valueRel f source target) :
    mutableBlockRel f old refs source target := by
  cases related <;> simp only [mutableBlockRel.eq_def] <;> constructor <;> assumption

/-- Filling a hole after related successful singleton evaluations preserves
the TMC state and heap relations. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_fill_hole_val"
  (fmap_as_finite_support_relation := [BviState.refs, f, fNext, fillMap])]
theorem evaluate_fill_hole_val {C F : Type} (e : Bvi.Exp)
    (f : HolFiniteMapExact Nat Nat) (fNext : HolFiniteMapExact Nat Nat)
    (env1 env2 : List Value) (source sourceNext : BviState (Nat × C) F)
    (target targetNext : BviState C F) (value relatedValue c : Value) (holePtr : Nat)
    (_sourceRun : evaluate [e] env1 source = (.val [value], sourceNext))
    (targetRun : evaluate [e] env2 target = (.val [relatedValue], targetNext))
    (_environments : envRel true f env1 env2) (_states : stateRel f source target)
    (submap : finiteSubmap f fNext) (values : valueRel fNext value relatedValue)
    (hole : holeHasVal f env1 env2 target.refs c) (unfinalised : holeNotFinalised target.refs holePtr)
    (unchanged : holesUnchangedExcept f target.refs targetNext.refs ∅)
    (still : holesStillNotFinalised f target.refs targetNext.refs)
    (fresh : onlyFresh f fNext target.refs) (nextStates : stateRel fNext sourceNext targetNext)
    (pointer : holEl env1.length env2 = .refPtr false holePtr) :
    ∃ (fillResult : BviResult) (fillMap : HolFiniteMapExact Nat Nat) (fillState : BviState C F),
      evaluate [fillHoleSource env1.length (env1.length + 1) e] env2 target = (fillResult, fillState) ∧
      optResRel fillMap (.val [value]) fillResult ∧ stateRel fillMap sourceNext fillState ∧
      finiteSubmap f fillMap ∧ onlyFresh f fillMap target.refs ∧
      holesUnchangedExcept f target.refs fillState.refs {holePtr} ∧
      holesStillNotFinalised f target.refs fillState.refs ∧
      ∃ fillValue, mutableBlockRel fillMap target.refs (fillState.refs.eraseEq holePtr) value fillValue ∧
        holeHasVal f env1 env2 fillState.refs fillValue := by
  classical
  obtain ⟨length, ptr, tag, finalised, left, right, ptrEq, idxEq, small, outside, found⟩ := hole
  rw [pointer] at ptrEq
  have ptrSame : ptr = holePtr := by simpa using ptrEq.symm
  subst ptr
  obtain ⟨nextFinalised, oldValue, nextFound, _⟩ :=
    unchanged holePtr tag finalised left c right outside found
  obtain ⟨otherTag, otherLeft, otherChild, otherRight, stillFound⟩ :=
    still holePtr outside unfinalised
  rw [nextFound] at stillFound
  simp only [Option.some.injEq, Ref.mutBlock.injEq] at stillFound
  have notFinal : nextFinalised = false := stillFound.2.1
  subst nextFinalised
  have allocated : holePtr ∈ target.refs.domain := by
    simp [HolFiniteMapExact.domain, found]
  have outsideNext : holePtr ∉ mapRange fNext := nonFresh_not_in_range f fNext target.refs holePtr allocated outside fresh
  have ptrBound : env1.length < env2.length := by omega
  have idxBound : env1.length + 1 < env2.length := by omega
  have ptrAt : env2[env1.length]? = some (.refPtr false holePtr) := by
    have atIndex : env2[env1.length] = .refPtr false holePtr := by
      simpa [holEl_eq_getElem env1.length env2 ptrBound] using pointer
    simpa [ptrBound] using congrArg some atIndex
  have idxAt : env2[env1.length + 1]? = some (.number (Int.ofNat left.length)) := by
    have atIndex : env2[env1.length + 1] = .number (Int.ofNat left.length) := by
      simpa [holEl_eq_getElem (env1.length + 1) env2 idxBound] using idxEq
    simpa [idxBound] using congrArg some atIndex
  let updated := targetNext.refs.updateEq (holePtr, .mutBlock tag false left relatedValue right)
  let filled := { targetNext with refs := updated }
  have sameDec : Classical.decEq Nat = instDecidableEqNat := by
    funext a b
    exact Subsingleton.elim _ _
  refine ⟨.val [unitValue], fNext, filled, ?_, ?_, ?_, submap, fresh, ?_, ?_, ?_⟩
  · exact evaluate_fillHole_update e env1.length (env1.length + 1) holePtr tag left oldValue right
      env2 target targetNext relatedValue targetRun ptrAt idxAt nextFound
  · simp [optResRel, unitValue]
  · exact stateRel_filled fNext sourceNext targetNext holePtr (.mutBlock tag false left relatedValue right)
      nextStates (fun i found => outsideNext ⟨i, found⟩)
  · have unchangedFilled := holesUnchanged_filled f target.refs targetNext.refs () holePtr tag false left relatedValue right
      finalised c unchanged found
    rw [sameDec] at unchangedFilled
    exact unchangedFilled
  · have stillFilled := holesStill_insert f target.refs targetNext.refs holePtr tag left relatedValue right still
    rw [sameDec] at stillFilled
    exact stillFilled
  · refine ⟨relatedValue, mutableBlockRel_of_valueRel fNext target.refs _ value relatedValue values, ?_⟩
    refine ⟨length, holePtr, tag, false, left, right, pointer, idxEq, small, outside, ?_⟩
    simp [filled, updated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- Filling a hole preserves related successful results and propagates related errors. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "evaluate_fill_hole"
  (fmap_as_finite_support_relation := [BviState.refs, f, fNext, fillMap])]
theorem evaluate_fill_hole {C F : Type} (e : Bvi.Exp)
    (f : HolFiniteMapExact Nat Nat) (fNext : HolFiniteMapExact Nat Nat)
    (env1 env2 : List Value) (source sourceNext : BviState (Nat × C) F)
    (target targetNext : BviState C F) (result targetResult : BviResult) (c : Value) (holePtr : Nat)
    (sourceRun : evaluate [e] env1 source = (result, sourceNext))
    (targetRun : evaluate [e] env2 target = (targetResult, targetNext))
    (environments : envRel true f env1 env2) (states : stateRel f source target)
    (submap : finiteSubmap f fNext)
    (results : resultRel (List.Forall₂ (valueRel fNext)) (eorRel fNext) result targetResult)
    (hole : holeHasVal f env1 env2 target.refs c) (unfinalised : holeNotFinalised target.refs holePtr)
    (unchanged : holesUnchangedExcept f target.refs targetNext.refs ∅)
    (still : holesStillNotFinalised f target.refs targetNext.refs)
    (fresh : onlyFresh f fNext target.refs) (nextStates : stateRel fNext sourceNext targetNext)
    (pointer : holEl env1.length env2 = .refPtr false holePtr) :
    ∃ (fillResult : BviResult) (fillMap : HolFiniteMapExact Nat Nat) (fillState : BviState C F),
      evaluate [fillHoleSource env1.length (env1.length + 1) e] env2 target = (fillResult, fillState) ∧
      optResRel fillMap result fillResult ∧ stateRel fillMap sourceNext fillState ∧
      finiteSubmap f fillMap ∧ onlyFresh f fillMap target.refs ∧
      holesUnchangedExcept f target.refs fillState.refs {holePtr} ∧
      holesStillNotFinalised f target.refs fillState.refs ∧
      ∀ value, result = .val [value] →
        ∃ fillValue, mutableBlockRel fillMap target.refs (fillState.refs.eraseEq holePtr) value fillValue ∧
          holeHasVal f env1 env2 fillState.refs fillValue := by
  cases result with
  | val sourceValues =>
    obtain ⟨value, rfl⟩ := evaluate_singleton e env1 source sourceNext sourceValues sourceRun
    cases targetResult with
    | err error => simp [resultRel] at results
    | val targetValues =>
      obtain ⟨relatedValue, rfl⟩ := evaluate_singleton e env2 target targetNext targetValues targetRun
      have valueRelated : valueRel fNext value relatedValue := by
        simp only [resultRel] at results
        cases results with
        | cons related _ => exact related
      obtain ⟨fillResult, fillMap, fillState, fillRun, optResult, finalStates, extension, only,
        holes, unfinalisedHoles, fillValue, mutable, filledHole⟩ :=
        evaluate_fill_hole_val e f fNext env1 env2 source sourceNext target targetNext value relatedValue c holePtr
          sourceRun targetRun environments states submap valueRelated hole unfinalised unchanged still fresh nextStates pointer
      refine ⟨fillResult, fillMap, fillState, fillRun, optResult, finalStates, extension, only,
        holes, unfinalisedHoles, ?_⟩
      intro returned eq
      cases eq
      exact ⟨fillValue, mutable, filledHole⟩
  | err error =>
    cases targetResult with
    | val targetValues => simp [resultRel] at results
    | err targetError =>
      have fillRun := evaluate_fillHole_error e env1.length (env1.length + 1) env2 target targetNext targetError targetRun
      refine ⟨.err targetError, fNext, targetNext, fillRun, ?_, nextStates, submap, fresh, ?_, still, ?_⟩
      · simpa [resultRel, optResRel] using results
      · exact holesUnchanged_subset f target.refs targetNext.refs ∅ {holePtr} unchanged (by simp)
      · intro value impossible; cases impossible

end Flapjack.Compiler.Backend.BviTmc.FillHole
