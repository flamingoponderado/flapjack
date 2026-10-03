import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnEval

namespace Flapjack.WordToStackProofs.CallReturnStackMoveClock
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs.CallReturnEval

/-- Genuine canonical target-state roundtrip for the representation qualifier;
no separate HOL declaration is claimed by this codec re-export. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original local Q.prove clock theorem. Arbitrary source states,
replacement clocks and all failure/result branches are retained. The entire
actual poststate is preserved except for the original clock replacement; no
useStack, access bound, successful execution or target poststate is assumed.
Evaluator closure inherits reals_as_rational_cuts; the structural clock proof
asserts no numerical FP correspondence. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "evaluate_stack_move_clock"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateStackMoveClock {width : Nat} [NeZero width] {C F : Type}
    (n start offset register : Nat) (target : StackSemStateFiniteExact width C F) (clock : Nat) :
    StackSemEvaluate.evaluate (stackMoveNative n start offset register .skip,
      {target with clock := clock}) =
      ((StackSemEvaluate.evaluate (stackMoveNative n start offset register .skip,target)).1,
       {(StackSemEvaluate.evaluate (stackMoveNative n start offset register .skip,target)).2
         with clock := clock}) := by
  suffices invariant : ClockFree (C := C) (F := F)
      (stackMoveNative (width := width) n start offset register .skip) by
    exact invariant target clock
  induction n generalizing start with
  | zero => exact clockFree_skip
  | succ n ih =>
    simp only [stackMoveNative]
    exact clockFree_seq _ _ (ih (start + 1))
      (clockFree_seq _ _ (clockFree_stackLoad _ _) (clockFree_stackStore _ _))

end Flapjack.WordToStackProofs.CallReturnStackMoveClock
