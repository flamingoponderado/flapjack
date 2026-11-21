module

public import Flapjack.Compiler.Encoders.Asm
public import Flapjack.Misc.Multiword
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas

@[expose] public section

/-! Word-bit facts used by the data-to-word bignum proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Misc.Multiword

/-- Testing a word against one checks that its low bit is clear. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "word_cmp_Test_1"
  (words_as_type_indexed_bitvec)]
theorem wordCmp_test_1 {width : Nat} [NeZero width] (w : BitVec width) :
    Compiler.Encoders.Asm.wordCmpHOL .test w 1 = true ↔ ¬ w.getLsbD 0 = true := by
  rw [← Compiler.Backend.StackAlloc.word_and_one_eq_0_iff w]
  change (w &&& 1 == 0) = true ↔ _
  simp

/-- The low bit of a Boolean-selected one or zero is the Boolean. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "word_bit_if_1_0"
  (words_as_type_indexed_bitvec)]
theorem wordBit_if_1_0 {width : Nat} [NeZero width] (b : Bool) :
    (if b then (1 : BitVec width) else 0).getLsbD 0 = true ↔ b = true := by
  cases b <;> simp [Nat.pos_of_ne_zero (NeZero.ne width)]

/-- Masking a word shifted right by four exposes its fourth bit. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "get_sign_word_lemma"
  (words_as_type_indexed_bitvec)]
theorem getSignWord_lemma {width : Nat} [NeZero width] (x : BitVec width) :
    goodDimindex width → (1 &&& x >>> (4 : Nat)) = if x.getLsbD 4 then (1 : BitVec width) else 0 := by
  intro good
  have big : 4 < width := by rcases good with h | h <;> omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases h : x.getLsbD 4 <;> by_cases i0 : i = 0 <;>
    simp [i0, h, hi, Nat.pos_of_ne_zero (NeZero.ne width)]

/-- A Boolean-selected one or zero is the Boolean's word embedding. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "if_eq_b2w"
  (words_as_type_indexed_bitvec)]
theorem if_eq_b2w {width : Nat} [NeZero width] (b : Bool) :
    (if b then (1 : BitVec width) else 0) = b2w b := by
  cases b <;> rfl

/-- A Boolean-selected zero or one is the natural embedding of its negation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "b2n_not"]
theorem b2n_not (c : Bool) : (if c then 0 else 1) = b2n (!c) := by
  cases c <;> rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
