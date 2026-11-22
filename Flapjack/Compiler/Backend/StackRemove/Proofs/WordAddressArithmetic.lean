module

public import Flapjack.Compiler.Backend.StackRemove
public import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas
public import Flapjack.Misc.Address

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

/-- HOL `byte_aligned_bytes_in_word_MULT` (`stack_removeProofScript.sml`):
multiplying a word by `bytes_in_word` leaves it byte aligned, for both good
dimensions. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "byte_aligned_bytes_in_word_MULT"
  (words_as_type_indexed_bitvec)]
theorem byteAlignedBytesInWordMult {width : Nat} [NeZero width] (w : BitVec width)
    (good : goodDimindex width) : holByteAligned (bytesInWord width * w) = true := by
  have hshift : bytesInWord width * w = w <<< wordShiftAmount width := by
    exact Compiler.Backend.WordGcFunctions.bytesInWord_mul_eq_shift w good
  have hlog : holLOG2 (width / 8) = wordShiftAmount width := by
    rcases good with h32 | h64
    · subst h32
      rw [holLOG2_eq_log2 (by omega)]
      rw [show (32 / 8 : Nat) = 2 ^ 2 by decide, Nat.log2_two_pow]
      rfl
    · subst h64
      rw [holLOG2_eq_log2 (by omega)]
      rw [show (64 / 8 : Nat) = 2 ^ 3 by decide, Nat.log2_two_pow]
      rfl
  have hle : wordShiftAmount width ≤ width := by
    rcases good with h32 | h64
    · subst h32
      simp [wordShiftAmount]
    · subst h64
      simp [wordShiftAmount]
  rw [hshift, holByteAligned, hlog, holAligned_iff]
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hle)]
  exact Nat.mul_mod_left _ _

/-- HOL `sub_rewrite` (`stack_removeProofScript.sml`): a non-negative
pointer difference cancels the two's-complement negation. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "sub_rewrite"
  (words_as_type_indexed_bitvec)]
theorem subRewrite {width : Nat} [NeZero width] (ptr ptr' : Nat) (le : ptr ≤ ptr') :
    -(1 : BitVec width) * BitVec.ofNat width ptr + BitVec.ofNat width ptr' =
      BitVec.ofNat width (ptr' - ptr) := by
  have hone : -(1 : BitVec width) * BitVec.ofNat width ptr = -BitVec.ofNat width ptr := by
    rw [BitVec.neg_mul]
    simp
  have sub : BitVec.ofNat width ptr' - BitVec.ofNat width ptr =
      BitVec.ofNat width (ptr' - ptr) := by
    rw [Flapjack.Misc.Address.wordArithLemma2]
    rw [if_neg (by omega)]
  rw [hone]
  rw [BitVec.add_comm]
  rw [← BitVec.sub_eq_add_neg]
  exact sub

/-- HOL `div_rewrite` (`stack_removeProofScript.sml`): a divisor no larger
than the dividend and greater than one gives a non-zero quotient. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "div_rewrite"]
theorem divRewrite (n x : Nat) (premise : n ≤ x ∧ 1 < n) : x / n ≠ 0 := by
  obtain ⟨hle, hgt⟩ := premise
  exact Nat.ne_of_gt (Nat.div_pos hle (by omega))

end Flapjack.Compiler.Backend.StackRemove.WordAddressArithmetic
