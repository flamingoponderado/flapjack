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

/-- Packed annotations distinguish all queries below both saturation limits. -/
theorem ptrBits_tagLength_eq64 (conf : Config) (actualTag actualLen tag len : Nat)
    (shiftBound : shiftLength conf < 64)
    (tagBound : tag < 2 ^ conf.tagBits - 1) (lenBound : len < 2 ^ conf.lenBits - 1) :
    ((ptrBits conf actualTag actualLen : BitVec 64) ||| 1) = (ptrBits conf tag len ||| 1) ↔
      actualTag = tag ∧ actualLen = len := by
  let satTag := if actualTag < 2 ^ conf.tagBits - 1 then actualTag else 2 ^ conf.tagBits - 1
  let satLen := if actualLen < 2 ^ conf.lenBits - 1 then actualLen else 2 ^ conf.lenBits - 1
  have satTagBound : satTag < 2 ^ conf.tagBits := by
    dsimp [satTag]
    have p := Nat.two_pow_pos conf.tagBits
    split <;> omega
  have satLenBound : satLen < 2 ^ conf.lenBits := by
    dsimp [satLen]
    have p := Nat.two_pow_pos conf.lenBits
    split <;> omega
  have tagSmall : tag < 2 ^ conf.tagBits := by have p := Nat.two_pow_pos conf.tagBits; omega
  have lenSmall : len < 2 ^ conf.lenBits := by have p := Nat.two_pow_pos conf.lenBits; omega
  constructor
  · intro same
    have lenEq : satLen = len := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases h : j < conf.lenBits
      · have index : j + 1 < 64 := by simp [shiftLength] at shiftBound; omega
        have bit := congrArg (fun x : BitVec 64 => x.getLsbD (j + 1)) same
        simp only [ptrBits_eq_inlined, tagBound, lenBound, ↓reduceIte,
          BitVec.getLsbD_or, BitVec.getLsbD_ofNat, Nat.testBit_mul_two_pow,
          index, decide_true, Bool.true_and] at bit
        have nt : ¬ 1 + conf.lenBits ≤ j + 1 := by omega
        simpa [satLen, nt, BitVec.getLsbD_one] using bit
      · have pow : 2 ^ conf.lenBits ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le satLenBound pow),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le lenSmall pow)]
    have tagEq : satTag = tag := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases h : j < conf.tagBits
      · have index : 1 + conf.lenBits + j < 64 := by simp [shiftLength] at shiftBound; omega
        have bit := congrArg (fun x : BitVec 64 => x.getLsbD (1 + conf.lenBits + j)) same
        simp only [ptrBits_eq_inlined, tagBound, lenBound, ↓reduceIte,
          BitVec.getLsbD_or, BitVec.getLsbD_ofNat, Nat.testBit_mul_two_pow,
          index, decide_true, Bool.true_and] at bit
        have pow : 2 ^ conf.lenBits ≤ 2 ^ (conf.lenBits + j) := Nat.pow_le_pow_right (by decide) (by omega)
        have lhs := Nat.testBit_lt_two_pow (lt_of_lt_of_le satLenBound pow)
        have rhs := Nat.testBit_lt_two_pow (lt_of_lt_of_le lenSmall pow)
        have sub : 1 + conf.lenBits + j - 1 = conf.lenBits + j := by omega
        simpa [satTag, satLen, sub, lhs, rhs, BitVec.getLsbD_one] using bit
      · have pow : 2 ^ conf.tagBits ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le satTagBound pow),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le tagSmall pow)]
    constructor
    · dsimp [satTag] at tagEq
      split at tagEq <;> omega
    · dsimp [satLen] at lenEq
      split at lenEq <;> omega
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A packed tag-and-length comparison agrees with related source blocks. -/
theorem stateRel64_getBlockFastTagLength {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name stamp actualTag tag len : Nat) (values : List DataSem.Value)
    (sourceRun : DataSem.getVar name source.locals = some (.block stamp actualTag values))
    (positive : 0 < len) (tagBound : tag < 2 ^ conf.tagBits - 1)
    (lenBound : len < 2 ^ conf.lenBits - 1) :
    ∃ word : BitVec 64, WordSemStateFiniteExact.getVar (adjustVar name) target = some (.word word) ∧
      ((word &&& BitVec.ofNat 64 (2 ^ (conf.lenBits + conf.tagBits + 1) - 1)) =
        (ptrBits conf tag len ||| 1) ↔ actualTag = tag ∧ values.length = len) := by
  by_cases empty : values = []
  · subst values
    obtain ⟨word, run, test⟩ := stateRel64_getBlockEmpty conf l1 l2 source target locs related name stamp actualTag [] sourceRun
    have low : word.getLsbD 0 = false := by
      simp only [List.length_nil, decide_true] at test
      change (word &&& (1 : BitVec 64) == 0) = true at test
      bv_decide
    refine ⟨word, run, ?_⟩
    have notZero : 0 ≠ len := by omega
    simp only [List.length_nil, notZero, and_false, iff_false]
    intro eq
    have bit := congrArg (fun x : BitVec 64 => x.getLsbD 0) eq
    have low' : word[0] = false := by simpa using low
    simp [low'] at bit
  · obtain ⟨word, ptr, run, encoding⟩ := stateRel64_getBlockPointer conf l1 l2 source target locs related
      name stamp actualTag values sourceRun empty
    refine ⟨word, run, ?_⟩
    rw [encoding, getAddr_tagLengthField64, ptrBits_combinedMask64]
    exact ptrBits_tagLength_eq64 conf actualTag values.length tag len related.2.2.2.2.2.2.2.1 tagBound lenBound

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
