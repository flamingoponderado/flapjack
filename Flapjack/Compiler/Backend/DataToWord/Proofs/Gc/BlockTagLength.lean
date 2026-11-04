import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockLength
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BlockPointer

/-! Constructor tag-and-length comparisons through concrete headers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A successfully encoded constructor header has its low marker bit set. -/
theorem encodeHeader_lowBit64 (conf : Config) (tag len : Nat) (header : BitVec 64)
    (encoded : encodeHeader conf tag len = some header) : header.getLsbD 0 = true := by
  unfold encodeHeader at encoded
  split at encoded
  · simp only [Option.some.injEq] at encoded
    subst header
    simp [makeHeader]
  · simp at encoded

/-- Successfully encoded source and query headers compare equal exactly when
both the source tag and the length match. -/
theorem encodedTagLength64 (conf : Config) (actualTag actualLen queryTag queryLen : Nat)
    (actualHeader queryHeader : BitVec 64) (configBound : conf.lenSize + 2 < 64)
    (actual : encodeHeader conf (4 * actualTag) actualLen = some actualHeader)
    (query : encodeHeader conf (4 * queryTag) queryLen = some queryHeader) :
    (actualHeader = queryHeader ↔ actualTag = queryTag ∧ actualLen = queryLen) := by
  have eq := Memory.encodeHeader_eq conf (4 * actualTag) actualLen (4 * queryTag) queryLen
    actualHeader queryHeader ⟨actual, query, configBound⟩
  constructor
  · intro same
    obtain ⟨tags, lens⟩ := eq.mp same
    exact ⟨by omega, lens⟩
  · rintro ⟨rfl, rfl⟩
    exact eq.mpr ⟨rfl, rfl⟩

/-- If a positive tag-length query cannot be encoded, it cannot match an
actual nonempty block whose header is encodable. -/
theorem unencodableTagLength64 (conf : Config) (actualTag actualLen queryTag queryLen : Nat)
    (actualHeader : BitVec 64)
    (actual : encodeHeader conf (4 * actualTag) actualLen = some actualHeader)
    (query : (encodeHeader conf (4 * queryTag) queryLen : Option (BitVec 64)) = none) :
    ¬ (actualTag = queryTag ∧ actualLen = queryLen) := by
  rintro ⟨rfl, rfl⟩
  rw [actual] at query
  cases query

/-- The complete pointer-field mask removes the heap index and preserves
both encoded fields and the pointer marker. -/
theorem getAddr_tagLengthField64 (conf : Config) (ptr tag len : Nat) :
    (Memory.getAddr conf ptr (.word (ptrBits conf tag len)) &&&
      BitVec.ofNat 64 (2 ^ (conf.lenBits + conf.tagBits + 1) - 1)) =
      ((ptrBits conf tag len &&& BitVec.ofNat 64 (2 ^ (conf.lenBits + conf.tagBits + 1) - 1)) ||| 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Memory.getAddr, getLowerBits_word_eq_mask, smallShiftLength,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  by_cases low : i < conf.lenBits + conf.tagBits + 1
  · have belowShift : i < shiftLength conf := by simp [shiftLength] at *; omega
    simp [low, belowShift]
  · have nonzero : i ≠ 0 := by omega
    simp [low, BitVec.getLsbD_one, nonzero]

/-- Below both saturation thresholds, the generated combined query is the
same packed annotation as the source-shaped pointer encoding. -/
theorem fastTagLengthQuery64 (conf : Config) (tag len : Nat)
    (tagBound : tag < 2 ^ conf.tagBits - 1) (lenBound : len < 2 ^ conf.lenBits - 1) :
    ((BitVec.ofNat 64 tag <<< (1 + conf.lenBits)) |||
      (BitVec.ofNat 64 len <<< 1) ||| 1) = (ptrBits conf tag len ||| 1) := by
  simp [ptrBits, maxoutBits, tagBound, lenBound]

/-- The source pointer annotation fits entirely within its combined tag and
length field mask. -/
theorem ptrBits_combinedMask64 (conf : Config) (tag len : Nat) :
    (ptrBits conf tag len &&& BitVec.ofNat 64 (2 ^ (conf.lenBits + conf.tagBits + 1) - 1)) =
      (ptrBits conf tag len : BitVec 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ptrBits_eq_inlined, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ofNat,
    Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  by_cases low : i < conf.lenBits + conf.tagBits + 1
  · simp [low]
  · have tagLimit : (if tag < 2 ^ conf.tagBits - 1 then tag else 2 ^ conf.tagBits - 1) < 2 ^ conf.tagBits := by
      have power := Nat.two_pow_pos conf.tagBits
      split <;> omega
    have lenLimit : (if len < 2 ^ conf.lenBits - 1 then len else 2 ^ conf.lenBits - 1) < 2 ^ conf.lenBits := by
      have power := Nat.two_pow_pos conf.lenBits
      split <;> omega
    have tagPower : 2 ^ conf.tagBits ≤ 2 ^ (i - (1 + conf.lenBits)) := Nat.pow_le_pow_right (by decide) (by omega)
    have lenPower : 2 ^ conf.lenBits ≤ 2 ^ (i - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have tagBit : (if tag < 2 ^ conf.tagBits - 1 then tag else 2 ^ conf.tagBits - 1).testBit (i - (1 + conf.lenBits)) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le tagLimit tagPower)
    have lenBit : (if len < 2 ^ conf.lenBits - 1 then len else 2 ^ conf.lenBits - 1).testBit (i - 1) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le lenLimit lenPower)
    simp [low, tagBit, lenBit]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
