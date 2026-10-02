import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.WordToStack.NativeCallArgs
import Flapjack.Compiler.Backend.StackProps.AllocArg

namespace Flapjack.WordToStackProofs
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

/-- Full original stack-slot movement implication, with arbitrary continuation
and unbounded natural slot/register arguments. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_move_alloc_arg"
  (words_as_type_indexed_bitvec)]
theorem stackMoveAllocArg {width : Nat} [NeZero width]
    (n st off i : Nat) (p : HolProg width) :
    allocArg p → allocArg (stackMoveNative n st off i p) := by
  intro hp
  induction n generalizing st with
  | zero => exact hp
  | succ n ih => simpa [stackMoveNative, allocArg] using ih (st + 1)

/-- Full original unrestricted recursive return-copy allocation-argument law. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "alloc_arg_copy_ret_aux"
  (words_as_type_indexed_bitvec)]
theorem allocArgCopyRetAux {width : Nat} [NeZero width] (k f n : Nat) :
    allocArg (copyRetAuxNative k f n : HolProg width) := by
  induction n with
  | zero => trivial
  | succ n ih => simpa [copyRetAuxNative, listSeq, allocArg] using ih

/-- Full original return-wrapper equivalence. Both Boolean modes and the
independent value/frame-tail carriers remain arbitrary; no allocation safety
or frame-size premise is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "alloc_arg_copy_ret"
  (words_as_type_indexed_bitvec)]
theorem allocArgCopyRet {width : Nat} [NeZero width] {β γ : Type}
    (perf b : Bool) (kf : Nat × Nat × γ) (vs : List β) (kont : HolProg width) :
    allocArg (copyRetNative perf b kf vs kont) ↔ allocArg kont := by
  by_cases zero : Flapjack.Compiler.Backend.WordToStack.numStackRet kf.1 vs = 0
  · simp [copyRetNative, zero]
  · simp [copyRetNative, zero, allocArg, allocArgCopyRetAux, seqStackFreeNative]

end Flapjack.WordToStackProofs
