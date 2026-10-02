import Flapjack.Compiler.Backend.StackProps.ExtractLabels
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.WordToStack.NativeReturn

namespace Flapjack.Compiler.Backend.WordToStack.Native.ExtractLabelsHelpers
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

/-- Flapjack proof infrastructure strengthening the source label-free stack-move
law to equality for any continuation. It has no independent HOL declaration. -/
theorem stackMoveLabels {width : Nat} [NeZero width]
    (n start offset i : Nat) (p : HolProg width) :
    extractLabels (stackMoveNative n start offset i p) = extractLabels p := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [stackMoveNative, extractLabels, ih]

/-- The complete original stack-move label-free implication. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "stack_move_no_labs" (words_as_type_indexed_bitvec)]
theorem stackMoveNoLabs {width : Nat} [NeZero width]
    (n a b c : Nat) (p : HolProg width) (h : extractLabels p = []) :
    extractLabels (stackMoveNative n a b c p) = [] := by
  rw [stackMoveLabels, h]

/-- Every descending return-slot copy is label-free, including zero copies. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "extract_labels_copy_ret_aux" (words_as_type_indexed_bitvec)]
theorem copyRetAuxLabels {width : Nat} [NeZero width] (k f n : Nat) :
    extractLabels (copyRetAuxNative k f n : HolProg width) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [copyRetAuxNative, listSeq, extractLabels, ih]

/-- The complete original return-copy wrapper preserves ordered continuation
labels. Both unused frame-tail and return-list element carriers remain arbitrary. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "extract_labels_copy_ret" (words_as_type_indexed_bitvec)]
theorem copyRetLabels {width : Nat} [NeZero width] {β γ : Type}
    (perf b : Bool) (kf : Nat × Nat × γ) (vs : List β) (kont : HolProg width) :
    extractLabels (copyRetNative perf b kf vs kont) = extractLabels kont := by
  simp only [copyRetNative]
  split
  · rfl
  · simp_all [extractLabels, copyRetAuxLabels, seqStackFreeNative]

/-- Flapjack proof infrastructure retaining arbitrary continuation labels through
native frame loads. It has no independent HOL declaration. -/
theorem stackLoadLabels {width : Nat} [NeZero width]
    (xs : List (Nat × Nat)) (p : HolProg width) :
    extractLabels (wStackLoadNative xs p) = extractLabels p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨r,i⟩; simp [wStackLoadNative, extractLabels, ih]

/-- The complete original frame-load Skip result. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "extract_labels_wStackLoad_Skip" (words_as_type_indexed_bitvec)]
theorem stackLoadSkipLabels {width : Nat} [NeZero width] (xs : List (Nat × Nat)) :
    extractLabels (wStackLoadNative xs (.skip : HolProg width)) = [] := by
  rw [stackLoadLabels]; rfl

/-- The complete original stack-move allocation result for arbitrary counts. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "extract_labels_stack_move_StackAlloc" (words_as_type_indexed_bitvec)]
theorem stackMoveAllocLabels {width : Nat} [NeZero width]
    (n start offset i k : Nat) :
    extractLabels (stackMoveNative n start offset i (.stackAlloc k : HolProg width)) = [] := by
  rw [stackMoveLabels]; rfl

end Flapjack.Compiler.Backend.WordToStack.Native.ExtractLabelsHelpers
