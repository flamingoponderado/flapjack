import Flapjack.Compiler.Backend.WordToStack.Proofs.CallDest
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

namespace Flapjack.WordToStackProofs.LoadRegister
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness



/-- Original register-1 stack-load transport, retaining the entire original
state relation and actual execution plus all clock/stack/bitmap/register
preservation conclusions. Actual stack bounds and the loaded value follow
from the original source lookup and full state relation, not extra premises.
The canonical finite maps and positive word dimensions are qualified;
coordinator source acceptance remains pending. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackLoad_wReg1"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWStackLoadWReg1 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame r reg : Nat) (loads : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (value : WordLocW width)
    (compiled : wReg1 r (k, f, frame) = (loads, reg))
    (even : r % 2 = 0)
    (sourceRead : WordSemStateFiniteExact.getVar r source = some value)
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wStackLoadNative loads .skip, target) = (none, post) ∧
      target.clock = post.clock ∧ stateRel ac k f frame source post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace ∧
      post.bitmaps = target.bitmaps ∧
      (∀ register, register ≠ k → StackSemStateOps.getVar register post =
        StackSemStateOps.getVar register target) ∧
      reg ≠ k + 1 ∧ StackSemStateOps.getVar reg post = some value := by
  by_cases below : r / 2 < k
  · simp only [wReg1, below, if_true, Prod.mk.injEq] at compiled
    obtain ⟨rfl, rfl⟩ := compiled
    refine ⟨target, StackSemEvaluate.evaluate_skip target, rfl, related, rfl, rfl, rfl,
      (fun _ _ => rfl), by omega, ?_⟩
    exact StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 r value
      ⟨related, sourceRead, even, below⟩
  · simp only [wReg1, below, if_false, Prod.mk.injEq] at compiled
    obtain ⟨rfl, rfl⟩ := compiled
    have placement := StateRelGetVar.stateRel_locals related r value sourceRead
    rw [if_neg below] at placement
    obtain ⟨_, slot, bound⟩ := placement
    rw [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at slot
    split at slot
    swap
    · cases slot
    have stackBound := (List.getElem?_eq_some_iff.mp slot).1
    have stackValue := (List.getElem?_eq_some_iff.mp slot).2
    have useStack : target.useStack = true := related.2.2.2.2.1
    refine ⟨StackSemStateOps.setVar k value target, ?_, rfl,
      CallDest.stateRel_setVar_of_ge k (Nat.le_refl _) value related, rfl, rfl, rfl, ?_, by omega, ?_⟩
    · rw [wStackLoadNative, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_stackLoad,
        if_neg (by simp [useStack]), dif_pos stackBound]
      simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
      rw [wStackLoadNative, StackSemEvaluate.evaluate_skip, stackValue]
    · intro register different
      simp [StackSemStateOps.getVar, StackSemStateOps.setVar, HolFiniteMapExact.updateEq,
        FUPDATE_HOL, different]
    · simp [StackSemStateOps.getVar, StackSemStateOps.setVar, HolFiniteMapExact.updateEq,
        FUPDATE_HOL]

/-- Flapjack infrastructure: unconditional native Seq reassociation for the
load-prefix induction; it does not claim a separate HOL original. -/
private theorem sequenceAssoc {width : Nat} [NeZero width] {C F : Type}
    (first second third : HolProg width) (target : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.seq first (.seq second third), target) =
      StackSemEvaluate.evaluate (.seq (.seq first second) third, target) := by
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases run : StackSemEvaluate.evaluate (first, target) with ⟨result, post⟩
  cases result
  · exact StackSemEvaluate.evaluate_seq second third post |>.trans
      (by rw [StackSemEvaluateClock.fixClockEvaluate])
  · rfl

/-- Original load-prefix continuation equation, for arbitrary lists, indices,
programs and states, including failed loads and all non-NONE outcomes.
The canonical finite maps and positive word dimensions are qualified;
coordinator source acceptance remains pending. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_wStackLoad_seq"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWStackLoadSeq {width : Nat} [NeZero width] {C F : Type}
    (loads : List (Nat × Nat)) (program : HolProg width)
    (target : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (wStackLoadNative loads program, target) =
      StackSemEvaluate.evaluate (.seq (wStackLoadNative loads .skip) program, target) := by
  induction loads generalizing target with
  | nil =>
    simp only [wStackLoadNative, StackSemEvaluate.evaluate_seq,
      StackSemEvaluate.evaluate_skip, StackSemControl.fixClock, Nat.min_self]
  | cons entry loads ih =>
    rcases entry with ⟨register, slot⟩
    change StackSemEvaluate.evaluate (.seq (.stackLoad register slot)
      (wStackLoadNative loads program), target) =
      StackSemEvaluate.evaluate (.seq (.seq (.stackLoad register slot)
        (wStackLoadNative loads .skip)) program, target)
    rw [← sequenceAssoc]
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
    rcases run : StackSemEvaluate.evaluate (.stackLoad register slot, target) with ⟨result, post⟩
    cases result
    · exact ih post
    · rfl

end Flapjack.WordToStackProofs.LoadRegister
