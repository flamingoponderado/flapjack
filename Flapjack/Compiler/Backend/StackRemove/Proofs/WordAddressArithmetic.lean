module

public import Flapjack.Compiler.Backend.StackRemove
public import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas
public import Flapjack.Misc.Alignment

@[expose] public section
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

/-- A multiple of the word's byte count is byte aligned, for every word,
including products that wrap. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "byte_aligned_bytes_in_word_MULT"
  (words_as_type_indexed_bitvec)]
theorem byteAlignedBytesInWordMult {width : Nat} [NeZero width] (w : BitVec width)
    (good : goodDimindex width) : holByteAligned (bytesInWord width * w) = true := by
  unfold holByteAligned holAligned
  rw [holAlign_eq_div, decide_eq_true_iff]
  rcases good with rfl | rfl
  · rw [show (32 : Nat) / 8 = 4 from rfl, show holLOG2 4 = 2 from holLOG_UNIQUE 2 4 2 ⟨by decide, by decide⟩]
    apply BitVec.eq_of_toNat_eq
    simp only [bytesInWord, BitVec.toNat_ofNat, BitVec.toNat_mul]
    omega
  · rw [show (64 : Nat) / 8 = 8 from rfl, show holLOG2 8 = 3 from holLOG_UNIQUE 2 8 3 ⟨by decide, by decide⟩]
    apply BitVec.eq_of_toNat_eq
    simp only [bytesInWord, BitVec.toNat_ofNat, BitVec.toNat_mul]
    omega

/-- Negated-scaled subtraction of naturals, as a word identity, when the
subtrahend does not exceed the minuend. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "sub_rewrite"
  (words_as_type_indexed_bitvec)]
theorem subRewrite {width : Nat} [NeZero width] (ptr ptr' : Nat) (le : ptr ≤ ptr') :
    (-(1#width) * BitVec.ofNat width ptr + BitVec.ofNat width ptr' : BitVec width) =
      BitVec.ofNat width (ptr' - ptr) := by
  have split : BitVec.ofNat width ptr' = BitVec.ofNat width (ptr' - ptr) + BitVec.ofNat width ptr := by
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  rw [split, BitVec.neg_mul, BitVec.one_mul, BitVec.add_comm (BitVec.ofNat width (ptr' - ptr)),
    ← BitVec.add_assoc, BitVec.add_comm (-_)]
  rw [BitVec.add_right_neg, BitVec.zero_add]

/-- Division by a divisor greater than one is nonzero when the dividend
is at least the divisor. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "div_rewrite"]
theorem divRewrite (n x : Nat) (h : n ≤ x ∧ 1 < n) : x / n ≠ 0 := by
  obtain ⟨le, gt⟩ := h
  exact Nat.ne_of_gt (Nat.div_pos le (by omega))

end Flapjack.Compiler.Backend.StackRemove.WordAddressArithmetic
