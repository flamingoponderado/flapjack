module

public import Flapjack.Compiler.Backend.DataToWord.Build
public import Flapjack.Compiler.Backend.DataToWord.Header
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Numbers
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordStrideAlignment
@[expose] public section

/-! Bit bounds and pointer annotations in the data-to-word memory proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataToWord

 /-- An all-ones mask has exactly the source interval of set bits. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ones_bit"
  (words_as_type_indexed_bitvec)]
theorem allOnes_bit {width : Nat} [NeZero width] (e b i : Nat) (hi : i < width) :
    (allOnes e b : BitVec width).getLsbD i = true ↔ b ≤ i ∧ i < e := by
  by_cases h : e ≤ b
  · simp [allOnes, h]
    omega
  · simp only [allOnes, h, ↓reduceIte, holWordSlice, getLsbD_holFcpWord,
      BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    simp
    omega

 /-- Every set maxout bit lies in its encoded field. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "maxout_bits_bit"
  (words_as_type_indexed_bitvec)]
theorem maxoutBits_bit {width : Nat} [NeZero width] (n l b i : Nat)
    (bit : (maxoutBits n l b : BitVec width).getLsbD i = true) (hi : i < width) :
    b ≤ i ∧ i < b + l := by
  by_cases h : n < 2 ^ l - 1
  · simp only [maxoutBits, h, ↓reduceIte, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and] at bit
    have bi : ¬ i < b := by
      intro hlt
      simp [hlt] at bit
    have low : b ≤ i := by omega
    have high : i < b + l := by
      by_contra hn
      have hln : l ≤ i - b := by omega
      have nlt : n < 2 ^ (i - b) := by
        have hp : 2 ^ l ≤ 2 ^ (i - b) := Nat.pow_le_pow_right (by decide) hln
        omega
      have hnbit : n.testBit (i - b) = false := Nat.testBit_lt_two_pow nlt
      simp [BitVec.getLsbD_ofNat, hnbit] at bit
    exact ⟨low, high⟩
  · have hbit : (allOnes (width := width) (b + l) b).getLsbD i = true := by
      simpa [maxoutBits, h] using bit
    exact (allOnes_bit (b + l) b i hi).mp hbit

 /-- Extracting pointer bits preserves the complete annotation and marker. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_lowerbits_ptrbits"
  (words_as_type_indexed_bitvec)]
theorem getLowerBits_ptrBits {width : Nat} [NeZero width] (conf : Config) (tag len : Nat) :
    getLowerBits conf (.word (ptrBits conf tag len : BitVec width)) = ptrBits conf tag len ||| 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases small : i < smallShiftLength conf
  · simp [getLowerBits, small, hi]
  · have high : smallShiftLength conf ≤ i := by omega
    have htag : (maxoutBits (width := width) tag conf.tagBits (1 + conf.lenBits)).getLsbD i = false := by
      cases hb : (maxoutBits (width := width) tag conf.tagBits (1 + conf.lenBits)).getLsbD i with
      | false => rfl
      | true =>
        have h := maxoutBits_bit tag conf.tagBits (1 + conf.lenBits) i hb hi
        simp only [smallShiftLength] at high
        omega
    have hlen : (maxoutBits (width := width) len conf.lenBits 1).getLsbD i = false := by
      cases hb : (maxoutBits (width := width) len conf.lenBits 1).getLsbD i with
      | false => rfl
      | true =>
        have h := maxoutBits_bit len conf.lenBits 1 i hb hi
        simp only [smallShiftLength] at high
        omega
    have htagElem : (maxoutBits (width := width) tag conf.tagBits (1 + conf.lenBits))[i] = false := by
      simpa [BitVec.getLsbD_eq_getElem hi] using htag
    have hlenElem : (maxoutBits (width := width) len conf.lenBits 1)[i] = false := by
      simpa [BitVec.getLsbD_eq_getElem hi] using hlen
    simp [getLowerBits, ptrBits, BitVec.getLsbD_extractLsb', small, hi, htagElem, hlenElem]

/-- Every set maxout bit is below the field end. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "maxout_bits_IMP"
  (words_as_type_indexed_bitvec)]
theorem maxoutBits_imp {width : Nat} [NeZero width] (tag k n i : Nat)
    (hi : i < width) (bit : (maxoutBits tag k n : BitVec width).getLsbD i = true) :
    i < n + k := (maxoutBits_bit tag k n i bit hi).2

/-- The constructor pointer exposes its full annotation bits. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "make_cons_ptr_thm"
  (words_as_type_indexed_bitvec)]
theorem makeConsPtr_eq {width : Nat} [NeZero width] (conf : Config) (f : BitVec width)
    (tag len : Nat) :
    Build.makeConsPtr conf f tag len = .word ((f <<< (shiftLength conf - wordShiftAmount width)) ||| 1 ||| ptrBits conf tag len) := by
  simp only [Build.makeConsPtr, getLowerBits_ptrBits, WordLocW.word.injEq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_or, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
