module

public import Flapjack.Compiler.Backend.DataToWord.Build
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordStrideAlignment
public import Flapjack.Compiler.Backend.BackendCommon
@[expose] public section

/-! Alignment and addition identities for constant-pointer construction. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- An aligned machine word is a word shifted by the architecture stride. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "byte_aligned_IMP_shift"
  (words_as_type_indexed_bitvec)]
theorem byteAligned_imp_shift {width : Nat} [NeZero width] (w : BitVec width)
    (aligned : holByteAligned w = true) (good : goodDimindex width) :
    ∃ v : BitVec width, w = v <<< wordShiftAmount width := by
  have shiftEq : holLOG2 (width / 8) = wordShiftAmount width := by
    rcases good with h | h
    · simp [h, wordShiftAmount, show holLOG2 4 = 2 from holLOG_UNIQUE 2 4 2 ⟨by decide, by decide⟩]
    · simp [h, wordShiftAmount, show holLOG2 8 = 3 from holLOG_UNIQUE 2 8 3 ⟨by decide, by decide⟩]
  have h : holAlign (wordShiftAmount width) w = w := by
    simpa [holByteAligned, holAligned, shiftEq] using aligned
  refine ⟨w >>> wordShiftAmount width, ?_⟩
  rw [← holAlign_eq_shift, h]

/-- A word with zero high bits is disjoint from a sufficiently shifted word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_and_lsr_0"
  (words_as_type_indexed_bitvec)]
theorem wordAndLslZero {width : Nat} [NeZero width] (k : Nat) (w n : BitVec width)
    (highZero : ∀ i, k ≤ i ∧ i < width → w.getLsbD i = false) :
    w &&& (n <<< k) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < k
  · simp [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, h]
  · have hz := highZero i ⟨by omega, hi⟩
    simp [BitVec.getLsbD_and, hz]

/-- The source pointer OR equals the corresponding aligned addition. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "make_ptr_add"
  (words_as_type_indexed_bitvec)]
theorem makePtr_add {width : Nat} [NeZero width] {α β : Type} (conf : Config)
    (n : BitVec width) (tag : α) (len : β)
    (aligned : holByteAligned n = true) (good : goodDimindex width)
    (shiftBound : wordShiftAmount width ≤ shiftLength conf) :
    Build.makePtr conf n tag len = .word ((n <<< (shiftLength conf - wordShiftAmount width)) + 1) := by
  obtain ⟨v, rfl⟩ := byteAligned_imp_shift n aligned good
  have shiftEq : wordShiftAmount width + (shiftLength conf - wordShiftAmount width) = shiftLength conf := by omega
  have zeroBits : (1 : BitVec width) &&& (v <<< shiftLength conf) = 0 := by
    apply wordAndLslZero
    intro i hi
    have hpos : 0 < shiftLength conf := by simp [shiftLength]
    simp [BitVec.getLsbD_one, show i ≠ 0 by omega]
  have zeroBits2 : (v <<< shiftLength conf) &&& (1 : BitVec width) = 0 := by
    simpa [BitVec.and_comm] using zeroBits
  simp only [Build.makePtr, ← BitVec.shiftLeft_add, shiftEq]
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ zeroBits2]

/-- The constructor pointer OR equals the corresponding aligned addition. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "make_cons_ptr_add"
  (words_as_type_indexed_bitvec)]
theorem makeConsPtr_add {width : Nat} [NeZero width] (conf : Config)
    (n : BitVec width) (tag len : Nat)
    (aligned : holByteAligned n = true) (good : goodDimindex width)
    (shiftBound : wordShiftAmount width ≤ shiftLength conf) :
    Build.makeConsPtr conf n tag len =
      .word ((n <<< (shiftLength conf - wordShiftAmount width)) + getLowerBits conf (.word (ptrBits conf tag len))) := by
  obtain ⟨v, rfl⟩ := byteAligned_imp_shift n aligned good
  have shiftEq : wordShiftAmount width + (shiftLength conf - wordShiftAmount width) = shiftLength conf := by omega
  let low := getLowerBits conf (.word (ptrBits conf tag len : BitVec width))
  have lowSmall : smallShiftLength conf ≤ shiftLength conf := by simp [smallShiftLength, shiftLength]
  have positive : 0 < smallShiftLength conf := by simp [smallShiftLength]
  have zeroBits : low &&& (v <<< shiftLength conf) = 0 := by
    apply wordAndLslZero
    intro i hi
    have notSmall : ¬ i < smallShiftLength conf := by omega
    have nz : i ≠ 0 := by omega
    simp [low, getLowerBits, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb', notSmall, nz]
  have zeroBits2 : (v <<< shiftLength conf) &&& low = 0 := by
    simpa [BitVec.and_comm] using zeroBits
  have marker : (1 : BitVec width) ||| low = low := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [low, getLowerBits, BitVec.getLsbD_or, Bool.or_comm]
  simp only [Build.makeConsPtr, ← BitVec.shiftLeft_add, shiftEq]
  change WordLocW.word (((v <<< shiftLength conf) ||| 1) ||| low) = WordLocW.word ((v <<< shiftLength conf) + low)
  rw [BitVec.or_assoc, marker, BitVec.add_eq_or_of_and_eq_zero _ _ zeroBits2]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
