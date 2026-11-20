module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- A successful header encoding has a bounded, recoverable length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "encode_header_IMP"
  (words_as_type_indexed_bitvec)]
theorem encodeHeaderImp {width : Nat} [NeZero width] (c : DataToWord.Config) (tag len : Nat)
    (hd : BitVec width) (encoded : encodeHeader c tag len = some hd)
    (bound : c.lenSize + 5 < width) (_good : goodDimindex width) :
    len < 2 ^ (width - 4) ∧ WordGcFunctions.decodeLength c hd = BitVec.ofNat width len := by
  simp only [encodeHeader] at encoded
  split at encoded
  next bounds =>
    have eq : makeHeader c (BitVec.ofNat width tag) len = hd := Option.some.inj encoded
    subst hd
    refine ⟨bounds.2.2.1, ?_⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have kpos : 5 < width - c.lenSize := by omega
    have shifted : width - c.lenSize + i - (width - c.lenSize) = i := by omega
    have widthPow : 2 < 2 ^ width := by
      have p := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ width by omega)
      change 4 ≤ 2 ^ width at p
      omega
    have twoMod : 2 % 2 ^ width = 2 := Nat.mod_eq_of_lt widthPow
    have tagBound : tag < 2 ^ (width - c.lenSize + i - 2) := by
      have p := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (show width - c.lenSize - 2 ≤ width - c.lenSize + i - 2 by omega)
      exact Nat.lt_of_lt_of_le bounds.1 p
    have tagZero := Nat.testBit_lt_two_pow tagBound
    have threeZero : Nat.testBit 3 (width - c.lenSize + i) = false := by
      apply Nat.testBit_lt_two_pow
      have p := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
        (show 2 ≤ width - c.lenSize + i by omega)
      change 4 ≤ 2 ^ (width - c.lenSize + i) at p
      omega
    have threeAt : (3 : BitVec width).getLsbD (width - c.lenSize + i) = false := by
      change (BitVec.ofNat width 3).getLsbD _ = false
      simp [BitVec.getLsbD_ofNat, threeZero]
    have tagAt : ((BitVec.ofNat width tag) <<< (2 : BitVec width)).getLsbD
        (width - c.lenSize + i) = false := by
      simp [BitVec.getLsbD_ofNat, twoMod, tagZero]
    simp only [WordGcFunctions.decodeLength, makeHeader, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
    rw [tagAt, threeAt]
    by_cases within : i < c.lenSize
    · have inRange : width - c.lenSize + i < width := by omega
      simp [hi, inRange, shifted, show ¬ width - c.lenSize + i < width - c.lenSize by omega]
    · have outRange : ¬ width - c.lenSize + i < width := by omega
      have lenBound : len < 2 ^ i := Nat.lt_of_lt_of_le bounds.2.2.2
        (Nat.pow_le_pow_right (by decide) (by omega))
      have lenZero := Nat.testBit_lt_two_pow lenBound
      simp [hi, outRange, lenZero]

  next => simp at encoded
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
