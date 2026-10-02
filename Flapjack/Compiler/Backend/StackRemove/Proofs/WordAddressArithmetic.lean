import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas
namespace Flapjack.Compiler.Backend.StackRemove.WordAddressArithmetic
open Flapjack Flapjack.Compiler.Backend.StackRemove
/-- Original inverse byte-scaling shift, retaining the good-dimension and no-wrap bound. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "bytes_in_word_word_shift"
  (words_as_type_indexed_bitvec)]
theorem bytesInWordWordShift {width : Nat} [NeZero width] (word : BitVec width)
    (hypothesis : goodDimindex width ∧ (bytesInWord width).toNat * word.toNat < 2 ^ width) :
    (bytesInWord width * word) >>> wordShiftAmount width = word := by
  exact Compiler.Backend.StackAlloc.bytesInWord_wordShift hypothesis
/-- Original unconditional word-offset equality, including modular natural conversion. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_offset_eq"
  (words_as_type_indexed_bitvec)]
theorem wordOffsetEq {width : Nat} [NeZero width] (count : Nat) :
    (wordOffset count : BitVec width) = bytesInWord width * BitVec.ofNat width count := by
  simp [wordOffset, bytesInWord, BitVec.ofNat_mul]
/-- Original forward word shift, with only its good-dimension premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "lsl_word_shift"
  (words_as_type_indexed_bitvec)]
theorem lslWordShift {width : Nat} [NeZero width] (word : BitVec width)
    (good : goodDimindex width) :
    word <<< wordShiftAmount width = word * bytesInWord width := by
  rw [BitVec.mul_comm]
  exact (Compiler.Backend.WordGcFunctions.bytesInWord_mul_eq_shift word good).symm
end Flapjack.Compiler.Backend.StackRemove.WordAddressArithmetic
