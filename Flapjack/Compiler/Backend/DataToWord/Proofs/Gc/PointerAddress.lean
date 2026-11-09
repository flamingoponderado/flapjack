module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Address
public import Flapjack.Compiler.Backend.WordGcFunctions

@[expose] public section

/-! Address facts needed for pointer cases of the collector simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_addr_and_1_not_0"
  (words_as_type_indexed_bitvec)]
theorem getAddr_and_one_ne_zero {width : Nat} [NeZero width] (conf : Config)
    (index : Nat) (value : WordLocW width) :
    ((1 : BitVec width) &&& getAddr conf index value) ≠ 0 := by
  have positive : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  intro equality
  have bit := congrArg (fun word : BitVec width => word.getLsbD 0) equality
  cases value <;> simp [getAddr, getLowerBits, positive] at bit

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "ptr_to_addr_get_addr"
  (words_as_type_indexed_bitvec)]
theorem ptrToAddr_getAddr {width : Nat} [NeZero width] (conf : Config)
    (curr : BitVec width) (index : Nat) (value : WordLocW width)
    (bounded : index * 2 ^ shiftLength conf < 2 ^ width) :
    WordGcFunctions.ptrToAddr conf curr (getAddr conf index value) =
      curr + BitVec.ofNat width index * wordSemBytesInWord := by
  simp [WordGcFunctions.ptrToAddr, getAddr, BitVec.ushiftRight_or_distrib,
    getLowerBits_shiftLength, bounded_shift_roundtrip index (shiftLength conf) bounded]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "NOT_is_fwd_ptr"
  (words_as_type_indexed_bitvec)]
theorem wordPayload_not_fwdPtr {headerWidth : Nat} {payloadWidth : Nat}
    [NeZero headerWidth] [NeZero payloadWidth] (conf : Config)
    (addresses : List (HeapAddress (WordLocW payloadWidth))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW payloadWidth)) (header : BitVec headerWidth)
    (words : List (WordLocW payloadWidth)) (valid : Bool)
    (encoded : wordPayload addresses len tag payload conf = (header, words, valid)) :
    wordSemIsFwdPtr (.word header) = false := by
  have positive : 0 < headerWidth := Nat.pos_of_ne_zero (NeZero.ne headerWidth)
  have bit3 : (3 : BitVec headerWidth).getLsbD 0 = true := by
    change (BitVec.ofNat headerWidth 3).getLsbD 0 = true
    simp [BitVec.getLsbD_ofNat, positive]
  have bit7 : (7 : BitVec headerWidth).getLsbD 0 = true := by
    change (BitVec.ofNat headerWidth 7).getLsbD 0 = true
    simp [BitVec.getLsbD_ofNat, positive]
  have bit23 : (23 : BitVec headerWidth).getLsbD 0 = true := by
    change (BitVec.ofNat headerWidth 23).getLsbD 0 = true
    simp [BitVec.getLsbD_ofNat, positive]
  have bit3' : (BitVec.ofNat headerWidth 3)[0]'positive = true := by
    simpa [BitVec.getLsbD_eq_getElem positive] using bit3
  have bit7' : (BitVec.ofNat headerWidth 7)[0]'positive = true := by
    simpa [BitVec.getLsbD_eq_getElem positive] using bit7
  have bit23' : (BitVec.ofNat headerWidth 23)[0]'positive = true := by
    simpa [BitVec.getLsbD_eq_getElem positive] using bit23
  have headerBit : header.getLsbD 0 = true := by
    cases tag <;> simp only [wordPayload, Prod.mk.injEq] at encoded <;>
      rcases encoded with ⟨rfl, _, _⟩ <;>
      simp [makeHeader, makeByteHeader, positive, bit3']
    all_goals split <;> split <;> simp_all
  cases fwd : wordSemIsFwdPtr (.word header) with
  | false => rfl
  | true =>
    have zero : header &&& 3 = 0 := by simpa [wordSemIsFwdPtr] using fwd
    have bit := congrArg (fun word : BitVec headerWidth => word.getLsbD 0) zero
    have headerBit' : header[0]'positive = true := by
      simpa [BitVec.getLsbD_eq_getElem positive] using headerBit
    simp [positive, bit3'] at bit
    rw [headerBit'] at bit
    contradiction

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
