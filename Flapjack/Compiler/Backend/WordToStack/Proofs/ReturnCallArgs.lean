import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.StackProps.CallArgs

namespace Flapjack.WordToStackProofs
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

/-- Full original stack movement preservation implication, with the exact
five original convention registers and arbitrary count, offsets and body. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "stack_move_call_args" (words_as_type_indexed_bitvec)]
theorem stackMoveCallArgs {width : Nat} [NeZero width]
    (n start offset i : Nat) (p : HolProg width) (continuation : callArgs p 1 2 3 4 0) :
    callArgs (stackMoveNative n start offset i p) 1 2 3 4 0 := by
  induction n generalizing start with
  | zero => exact continuation
  | succ n ih =>
      simpa only [stackMoveNative, callArgs, and_self, and_true] using ih (start + 1)

/-- Full original descending return-copy convention theorem for every count
and offset, retaining the positive-width native word carrier. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_aux_call_args" (words_as_type_indexed_bitvec)]
theorem copyRetAuxCallArgs {width : Nat} [NeZero width] (k f n : Nat) :
    callArgs (copyRetAuxNative k f n : HolProg width) 1 2 3 4 0 := by
  induction n with
  | zero => trivial
  | succ n ih => simpa only [copyRetAuxNative, listSeq, callArgs, true_and] using ih

/-- Full original iff for return-copy/free wrapping. Both Boolean modes and
independent return-value/frame-tail types are retained; no continuation guard
is added, so failing calling conventions are preserved as well. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_call_args" (words_as_type_indexed_bitvec)]
theorem copyRetCallArgs {width : Nat} [NeZero width] {β γ : Type}
    (perf isHandle : Bool) (frame : Nat × Nat × γ) (vs : List β) (kont : HolProg width) :
    callArgs (copyRetNative perf isHandle frame vs kont) 1 2 3 4 0 ↔
      callArgs kont 1 2 3 4 0 := by
  simp only [copyRetNative]
  split
  · rfl
  · simp only [callArgs, copyRetAuxCallArgs, true_and, seqStackFreeNative]
    split <;> simp [callArgs]

end Flapjack.WordToStackProofs
