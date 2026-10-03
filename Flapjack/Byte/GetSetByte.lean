import Flapjack.Byte.SetByte

/-! Original byte read-after-write law (`HOL/src/n-bit/byteScript.sml:158`),
over arbitrary word dimensions of at least eight bits, and its bit-level
infrastructure. -/
namespace Flapjack.HolByte

/-- A byte index leaves room for a whole byte below the word dimension;
Flapjack infrastructure for the `i + byte_index a be < dimindex` step of the
original proof. -/
theorem byteIndex_add_le {width : Nat} [NeZero width] (h8 : 8 ≤ width)
    (address : BitVec width) (bigEndian : Bool) :
    byteIndex address bigEndian + 8 ≤ width := by
  have hd : 0 < width / 8 := Nat.div_pos h8 (by decide)
  have hm : address.toNat % (width / 8) < width / 8 := Nat.mod_lt _ hd
  have hw : 8 * (width / 8) ≤ width := Nat.mul_div_le width 8
  dsimp only [byteIndex]
  split <;> omega

/-- Every in-range bit of `set_byte`, unfolded from the literal definition;
Flapjack infrastructure. -/
theorem getLsbD_setByte {width : Nat} [NeZero width] (address : BitVec width)
    (byte : BitVec 8) (word : BitVec width) (bigEndian : Bool) (j : Nat) (hj : j < width) :
    (setByte address byte word bigEndian).getLsbD j =
      (decide (byteIndex address bigEndian + 8 ≤ j) && word.getLsbD j ||
        (decide (byteIndex address bigEndian ≤ j) &&
          byte.getLsbD (j - byteIndex address bigEndian)) ||
        decide (j < byteIndex address bigEndian) && word.getLsbD j) := by
  have h1 := wordSliceAlt_bit width (byteIndex address bigEndian + 8) word ⟨j, hj⟩
  have h2 := wordSliceAlt_bit (byteIndex address bigEndian) 0 word ⟨j, hj⟩
  simp only at h1 h2
  simp only [setByte, BitVec.getLsbD_or, h1, h2, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  by_cases hlo : byteIndex address bigEndian ≤ j
  · have hn : ¬ j < byteIndex address bigEndian := by omega
    simp [hlo, hn, show j - byteIndex address bigEndian < width by omega]
  · have hn : j < byteIndex address bigEndian := by omega
    simp [hlo, hn, show ¬ byteIndex address bigEndian + 8 ≤ j by omega]

@[hol "HOL/src/n-bit/byteScript.sml" "get_byte_set_byte"
  (words_as_type_indexed_bitvec)]
theorem getByte_setByte {width : Nat} [NeZero width] (a : BitVec width) (b : BitVec 8)
    (w : BitVec width) (be : Bool) :
    8 ≤ width → getByte a (setByte a b w be) be = b := by
  intro h8
  have hle := byteIndex_add_le h8 a be
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getByte, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]
  rw [getLsbD_setByte a b w be _ (by omega)]
  simp [show ¬ byteIndex a be + 8 ≤ byteIndex a be + i by omega,
    show ¬ byteIndex a be + i < byteIndex a be by omega]

end Flapjack.HolByte
