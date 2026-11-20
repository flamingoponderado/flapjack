module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Address
import Mathlib.Tactic.NormNum

@[expose] public section

/-! Decoding the length encoded in a byte-array header. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

private theorem shiftNat {width : Nat} [NeZero width] (n s k : Nat) (hs : s ≤ width)
    (hn : n < 2 ^ (width - s)) :
    (((BitVec.ofNat width n) <<< s) >>> (s + k)).toNat = n / 2 ^ k := by
  have nlt : n < 2 ^ width := Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega))
  have shifted : n * 2 ^ s < 2 ^ width := by
    have h := Nat.mul_lt_mul_of_pos_right hn (Nat.two_pow_pos s)
    rw [← Nat.pow_add, Nat.sub_add_cancel hs] at h
    exact h
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt nlt, Nat.shiftLeft_eq, Nat.mod_eq_of_lt shifted, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_add, Nat.mul_comm (2 ^ s) (2 ^ k), Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)]

private theorem decodeAux {width : Nat} [NeZero width] (n s k : Nat) (tag : BitVec width)
    (hs : s ≤ width) (hn : n < 2 ^ (width - s)) (ht : tag.toNat < 2 ^ (s + k)) :
    ((((BitVec.ofNat width n) <<< s) ||| tag) >>> (s + k)).toNat = n / 2 ^ k := by
  have zero : tag >>> (s + k) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt ht]
  rw [BitVec.ushiftRight_or_distrib, zero]
  simpa using shiftNat (width := width) n s k hs hn

/-- The decoded byte-array length equals the allocated word count. This
Flapjack helper supplies the concrete byte-allocation proof. -/
theorem decodeLength_makeByteHeader_exact {width : Nat} [NeZero width] (conf : Config) (flag : Bool) (len : Nat) :
    goodDimindex width ∧ conf.lenSize + 7 < width ∧
      len + 2 ^ wordShiftAmount width < 2 ^ (conf.lenSize + wordShiftAmount width) →
    (WordGcFunctions.decodeLength conf (makeByteHeader conf flag len) : BitVec width).toNat = len / (width / 8) + 1 := by
  rintro ⟨good, config, bound⟩
  rcases good with hw | hw <;> subst width
  · have hsize : conf.lenSize + 2 ≤ 32 := by omega
    have hs : 32 - 2 - conf.lenSize ≤ 32 := by omega
    have shiftEq : 32 - 2 - conf.lenSize + 2 = 32 - conf.lenSize := by omega
    have hn : len + 4 < 2 ^ (32 - (32 - 2 - conf.lenSize)) := by
      have e : 32 - (32 - 2 - conf.lenSize) = conf.lenSize + 2 := by omega
      simpa [wordShiftAmount, e] using bound
    have ht : (if flag then (7 : BitVec 32) else 23).toNat < 2 ^ (32 - conf.lenSize) := by
      have power : 2 ^ 5 ≤ 2 ^ (32 - conf.lenSize) := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num at power
      cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte, show (23 : BitVec 32).toNat = 23 by decide, show (7 : BitVec 32).toNat = 7 by decide] <;> omega
    have decoded := decodeAux (width := 32) (len + 4) (32 - 2 - conf.lenSize) 2
      (if flag then 7 else 23) hs hn (by simpa [shiftEq] using ht)
    rw [shiftEq] at decoded
    have decodedEq : (WordGcFunctions.decodeLength conf (makeByteHeader conf flag len) : BitVec 32).toNat =
        (len + 4) / 4 := by simpa [WordGcFunctions.decodeLength, makeByteHeader] using decoded
    rw [decodedEq]
    norm_num
  · have hsize : conf.lenSize + 3 ≤ 64 := by omega
    have hs : 64 - 3 - conf.lenSize ≤ 64 := by omega
    have shiftEq : 64 - 3 - conf.lenSize + 3 = 64 - conf.lenSize := by omega
    have hn : len + 8 < 2 ^ (64 - (64 - 3 - conf.lenSize)) := by
      have e : 64 - (64 - 3 - conf.lenSize) = conf.lenSize + 3 := by omega
      simpa [wordShiftAmount, e] using bound
    have ht : (if flag then (7 : BitVec 64) else 23).toNat < 2 ^ (64 - conf.lenSize) := by
      have power : 2 ^ 5 ≤ 2 ^ (64 - conf.lenSize) := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num at power
      cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte, show (23 : BitVec 64).toNat = 23 by decide, show (7 : BitVec 64).toNat = 7 by decide] <;> omega
    have decoded := decodeAux (width := 64) (len + 8) (64 - 3 - conf.lenSize) 3
      (if flag then 7 else 23) hs hn (by simpa [shiftEq] using ht)
    rw [shiftEq] at decoded
    have decodedEq : (WordGcFunctions.decodeLength conf (makeByteHeader conf flag len) : BitVec 64).toNat =
        (len + 8) / 8 := by simpa [WordGcFunctions.decodeLength, makeByteHeader] using decoded
    rw [decodedEq]
    norm_num

@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "decode_length_make_byte_header"
  (words_as_type_indexed_bitvec)]
theorem decodeLength_makeByteHeader {width : Nat} [NeZero width] (conf : Config) (flag : Bool) (len : Nat) :
    goodDimindex width ∧ conf.lenSize + 7 < width ∧
      len + 2 ^ wordShiftAmount width < 2 ^ (conf.lenSize + wordShiftAmount width) →
    len ≤ (WordGcFunctions.decodeLength conf (makeByteHeader conf flag len) : BitVec width).toNat * (width / 8) ∧
      (WordGcFunctions.decodeLength conf (makeByteHeader conf flag len) : BitVec width).toNat ≤ len / (width / 8) + 1 := by
  rintro ⟨good, config, bound⟩
  have exactLength := decodeLength_makeByteHeader_exact conf flag len ⟨good, config, bound⟩
  rw [exactLength]
  rcases good with h | h <;> subst width <;> norm_num <;> omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
