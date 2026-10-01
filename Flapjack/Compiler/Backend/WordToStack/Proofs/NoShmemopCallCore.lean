import Flapjack.Compiler.Backend.WordToStack.NativeReturn
import Flapjack.Compiler.Backend.WordToStack.NativePerf
import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

/-- Full original descending return-slot copy preservation. All counts and
frame offsets remain unrestricted, including saturated subtraction callers. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_aux_no_shmemop" (words_as_type_indexed_bitvec)]
theorem copyRetAuxNoShmemop {width : Nat} [NeZero width] (k f n : Nat) :
    noShmemop (copyRetAuxNative k f n : HolProg width) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [copyRetAuxNative, listSeq, noShmemop, ih]

/-- Literal instrumentation syntax contains no shared-memory operation.
This does not establish evaluation correctness of the instrumentation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "perf_call_prefix_no_shmemop" (words_as_type_indexed_bitvec)]
theorem perfCallPrefixNoShmemop {width : Nat} [NeZero width] (l1 l2 k : Nat) :
    noShmemop (perfCallPrefixNative l1 l2 k : HolProg width) = true := rfl

/-- Full original instrumentation suffix predicate, on every positive width. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "perf_call_suffix_no_shmemop" (words_as_type_indexed_bitvec)]
theorem perfCallSuffixNoShmemop {width : Nat} [NeZero width] :
    noShmemop (perfCallSuffixNative : HolProg width) = true := rfl

end Flapjack.Compiler.Backend.WordToStack.Native
