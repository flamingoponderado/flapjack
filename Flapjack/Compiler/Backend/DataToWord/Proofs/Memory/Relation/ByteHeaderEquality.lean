module

public import Flapjack.HolRef
import Mathlib.Data.Nat.Bitwise
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteHeaderDecode
public import Flapjack.Compiler.Backend.DataToWord.Build
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

/-! Equality of encoded byte-array lengths. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Cancel a left shift when neither natural-number encoding overflows. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem shiftedInject {width : Nat} (k a b : Nat)
    (ha : a * 2 ^ k < 2 ^ width) (hb : b * 2 ^ k < 2 ^ width)
    (same : (BitVec.ofNat width a <<< k) = (BitVec.ofNat width b <<< k)) : a = b := by
  have power : 0 < 2 ^ k := Nat.two_pow_pos k
  have aSmall : a < 2 ^ width := by nlinarith
  have bSmall : b < 2 ^ width := by nlinarith
  have eq := congrArg BitVec.toNat same
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt aSmall, Nat.mod_eq_of_lt bSmall, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at eq
  exact Nat.eq_of_mul_eq_mul_right power eq

/-- Bound the 32-bit byte-header length field using the source byte length. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem byteLenBound4 (n c : Nat) (h : n / 4 + 1 < 2 ^ c) :
    n + 4 < 2 ^ (c + 2) := by
  rw [pow_add]
  norm_num
  omega

/-- Bound the 64-bit byte-header length field using the source byte length. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem byteLenBound8 (n c : Nat) (h : n / 8 + 1 < 2 ^ c) :
    n + 8 < 2 ^ (c + 3) := by
  rw [pow_add]
  norm_num
  omega
/-- Cancel low tag bits from equal shifted words. This private cancellation form is the contrapositive of the local HOL `or_seven_eq`, rather than a separate port of its stated implication. -/
private theorem orSevenCancel {width : Nat} (x y : BitVec width) (k : Nat) (hk : 2 < k)
    (h : (x <<< k) ||| 7 = (y <<< k) ||| 7) : x <<< k = y <<< k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have eq := congrArg (fun v : BitVec width => v.getLsbD i) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft] at eq
  by_cases low : i < k
  · simp [BitVec.getLsbD_shiftLeft, low]
  · have large : 3 ≤ i := by omega
    have pow : 8 ≤ 2 ^ i := by
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) large
      simpa using h
    have sevenNat : Nat.testBit 7 i = false := Nat.testBit_eq_false_of_lt (by omega)
    have seven : (7 : BitVec width).getLsbD i = false := by
      rw [show (7 : BitVec width) = BitVec.ofNat width 7 from rfl]
      simp [BitVec.getLsbD_ofNat, sevenNat]
    change (_ || (7 : BitVec width).getLsbD i) = (_ || (7 : BitVec width).getLsbD i) at eq
    rw [seven, Bool.or_false, Bool.or_false] at eq
    simpa only [BitVec.getLsbD_shiftLeft] using eq

/-- Show a shifted length remains below the word modulus. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem shiftBound (width c extra a : Nat) (fits : c + extra ≤ width)
    (bound : a < 2 ^ (c + extra)) : a * 2 ^ (width - extra - c) < 2 ^ width := by
  have lengths : c + extra + (width - extra - c) = width := by omega
  have h := Nat.mul_lt_mul_of_pos_right bound (Nat.two_pow_pos (width - extra - c))
  simpa [← pow_add, lengths] using h

/-- Byte-array headers at valid lengths are equal exactly when the byte lengths are equal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "make_byte_header_eq"
  (words_as_type_indexed_bitvec)]
theorem makeByteHeader_eq {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (m n : Nat)
    (h : Build.byteLen width m < 2 ^ conf.lenSize ∧
      Build.byteLen width m < 2 ^ (width - 4) ∧
      Build.byteLen width n < 2 ^ conf.lenSize ∧
      Build.byteLen width n < 2 ^ (width - 4) ∧
      goodDimindex width ∧
      2 < width - (if width = 32 then 2 else 3) - conf.lenSize) :
    ((makeByteHeader conf true m : BitVec width) = makeByteHeader conf true n ↔ m = n) := by
  constructor
  · intro equal
    obtain ⟨hm, _, hn, _, good, limit⟩ := h
    rcases good with hw | hw
    · subst width
      have hk : 2 < 32 - 2 - conf.lenSize := by simpa using limit
      have fits : conf.lenSize + 2 ≤ 32 := by omega
      have hm1 : m + 4 < 2 ^ (conf.lenSize + 2) := byteLenBound4 m conf.lenSize (by simpa [Build.byteLen] using hm)
      have hn1 : n + 4 < 2 ^ (conf.lenSize + 2) := byteLenBound4 n conf.lenSize (by simpa [Build.byteLen] using hn)
      have ms := shiftBound 32 conf.lenSize 2 (m + 4) fits hm1
      have ns := shiftBound 32 conf.lenSize 2 (n + 4) fits hn1
      have shifted : (BitVec.ofNat 32 (m + 4) <<< (32 - 2 - conf.lenSize)) =
          (BitVec.ofNat 32 (n + 4) <<< (32 - 2 - conf.lenSize)) := by
        apply orSevenCancel _ _ _ hk
        simpa [makeByteHeader] using equal
      have result := shiftedInject (32 - 2 - conf.lenSize) (m + 4) (n + 4) ms ns shifted
      omega
    · subst width
      have hk : 2 < 64 - 3 - conf.lenSize := by simpa using limit
      have fits : conf.lenSize + 3 ≤ 64 := by omega
      have hm1 : m + 8 < 2 ^ (conf.lenSize + 3) := byteLenBound8 m conf.lenSize (by simpa [Build.byteLen] using hm)
      have hn1 : n + 8 < 2 ^ (conf.lenSize + 3) := byteLenBound8 n conf.lenSize (by simpa [Build.byteLen] using hn)
      have ms := shiftBound 64 conf.lenSize 3 (m + 8) fits hm1
      have ns := shiftBound 64 conf.lenSize 3 (n + 8) fits hn1
      have shifted : (BitVec.ofNat 64 (m + 8) <<< (64 - 3 - conf.lenSize)) =
          (BitVec.ofNat 64 (n + 8) <<< (64 - 3 - conf.lenSize)) := by
        apply orSevenCancel _ _ _ hk
        simpa [makeByteHeader] using equal
      have result := shiftedInject (64 - 3 - conf.lenSize) (m + 8) (n + 8) ms ns shifted
      omega
  · intro eq; subst n; rfl
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
