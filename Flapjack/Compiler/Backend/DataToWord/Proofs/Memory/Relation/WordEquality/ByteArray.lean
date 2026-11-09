import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordCompare
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArray
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueArray
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueEquality

/-! Comparison of packed byte-array payloads. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Misc.Multiword
open Classical
noncomputable section

/-- Recover an in-range length bit from a byte-array header. -/
theorem byteHeaderLengthBit {width : Nat} [NeZero width] (conf : DataToWord.Config) (flag : Bool)
    (len i : Nat) (good : goodDimindex width) (configBound : conf.lenSize + 7 < width)
    (hi : i < conf.lenSize + (if width = 32 then 2 else 3)) :
    (DataToWord.makeByteHeader (width := width) conf flag len).getLsbD
      (i + (width - (if width = 32 then 2 else 3) - conf.lenSize)) =
      (len + 2 ^ (if width = 32 then 2 else 3)).testBit i := by
  rcases good with hw | hw <;> subst width
  · have pos : i + (32 - 2 - conf.lenSize) < 32 := by simp at hi; omega
    have high : 5 ≤ i + (32 - 2 - conf.lenSize) := by omega
    have iBound : i < 32 := by simp at hi; omega
    have notLess : ¬ i + (32 - 2 - conf.lenSize) < 32 - 2 - conf.lenSize := by omega
    have pow := Nat.pow_le_pow_right (n := 2) (by decide) high
    have z7 : (7 : Nat).testBit (i + (32 - 2 - conf.lenSize)) = false := Nat.testBit_lt_two_pow (by omega)
    have z23 : (23 : Nat).testBit (i + (32 - 2 - conf.lenSize)) = false := Nat.testBit_lt_two_pow (by omega)
    cases flag <;> simp [DataToWord.makeByteHeader, pos, notLess]
    all_goals simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
      Nat.testBit_mod_two_pow, iBound, decide_true, Bool.true_and, z7, z23, Bool.or_false]
  · have pos : i + (64 - 3 - conf.lenSize) < 64 := by simp at hi; omega
    have high : 5 ≤ i + (64 - 3 - conf.lenSize) := by omega
    have iBound : i < 64 := by simp at hi; omega
    have notLess : ¬ i + (64 - 3 - conf.lenSize) < 64 - 3 - conf.lenSize := by omega
    have pow := Nat.pow_le_pow_right (n := 2) (by decide) high
    have z7 : (7 : Nat).testBit (i + (64 - 3 - conf.lenSize)) = false := Nat.testBit_lt_two_pow (by omega)
    have z23 : (23 : Nat).testBit (i + (64 - 3 - conf.lenSize)) = false := Nat.testBit_lt_two_pow (by omega)
    cases flag <;> simp [DataToWord.makeByteHeader, pos, notLess]
    all_goals simp only [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat,
      Nat.testBit_mod_two_pow, iBound, decide_true, Bool.true_and, z7, z23, Bool.or_false]

/-- Equal valid byte-array headers have equal byte lengths, even when their
    comparison flags differ. -/
theorem byteHeaderLengthInjective {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (flag1 flag2 : Bool) (len1 len2 : Nat) (good : goodDimindex width)
    (configBound : conf.lenSize + 7 < width)
    (bound1 : len1 + 2 ^ (if width = 32 then 2 else 3) <
      2 ^ (conf.lenSize + (if width = 32 then 2 else 3)))
    (bound2 : len2 + 2 ^ (if width = 32 then 2 else 3) <
      2 ^ (conf.lenSize + (if width = 32 then 2 else 3)))
    (same : DataToWord.makeByteHeader (width := width) conf flag1 len1 =
      DataToWord.makeByteHeader conf flag2 len2) : len1 = len2 := by
  have lengths : len1 + 2 ^ (if width = 32 then 2 else 3) = len2 + 2 ^ (if width = 32 then 2 else 3) := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < conf.lenSize + (if width = 32 then 2 else 3)
    · have bits := congrArg (fun w : BitVec width => w.getLsbD
          (i + (width - (if width = 32 then 2 else 3) - conf.lenSize))) same
      rw [byteHeaderLengthBit conf flag1 len1 i good configBound hi,
        byteHeaderLengthBit conf flag2 len2 i good configBound hi] at bits
      exact bits
    · have power : 2 ^ (conf.lenSize + (if width = 32 then 2 else 3)) ≤ 2 ^ i :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have first : (len1 + 2 ^ (if width = 32 then 2 else 3)).testBit i = false :=
        Nat.testBit_lt_two_pow (by omega)
      have second : (len2 + 2 ^ (if width = 32 then 2 else 3)).testBit i = false :=
        Nat.testBit_lt_two_pow (by omega)
      rw [first, second]
  omega

/-- Packing preserves the number of payload words. -/
private theorem packedLength {width : Nat} [NeZero width] (be : Bool)
    (words : List (BitVec width)) (bytes : List (BitVec 8)) :
    (DataToWord.writeBytes bytes words be).length = words.length := by
  induction words generalizing bytes with
  | nil => rfl
  | cons x xs ih => simp [DataToWord.writeBytes, ih]

/-- Comparing two separated packed payloads returns one exactly when their
    byte sequences agree. This is Flapjack infrastructure for the original
    reference-equality simulation. -/
theorem byteArrayWordEqualityLoop {width : Nat} [NeZero width] (be : Bool)
    (words : List (BitVec width)) (bytes1 bytes2 : List (BitVec 8))
    (frame1 frame2 : ((BitVec width × WordLocW width) → Prop) → Prop)
    (a1 a2 : BitVec width) (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (good : goodDimindex width) (sameLength : bytes1.length = bytes2.length)
    (capacity : bytes1.length ≤ words.length * (width / 8))
    (wordCount : words.length ≤ bytes1.length / (width / 8) + 1)
    (bound : words.length < 2 ^ width)
    (first : SetSep.star (Misc.wordList (a1 + StackRemove.bytesInWord width)
      ((DataToWord.writeBytes bytes1 words be).map WordLocW.word)) frame1
      (SetSep.fun2Set (memory, fun a => domain a = true)))
    (second : SetSep.star (Misc.wordList (a2 + StackRemove.bytesInWord width)
      ((DataToWord.writeBytes bytes2 words be).map WordLocW.word)) frame2
      (SetSep.fun2Set (memory, fun a => domain a = true))) :
    ∃ result : BitVec width,
      wordCmpLoop (BitVec.ofNat width words.length)
        (a1 + StackRemove.bytesInWord width * BitVec.ofNat width words.length)
        (a2 + StackRemove.bytesInWord width * BitVec.ofNat width words.length) domain memory = some result ∧
      (bytes1 = bytes2 ↔ result = 1) := by
  let xs := DataToWord.writeBytes bytes1 words be
  let ys := DataToWord.writeBytes bytes2 words be
  have xsLength : xs.length = words.length := packedLength be words bytes1
  have ysLength : ys.length = words.length := packedLength be words bytes2
  have lengths : xs.length = ys.length := xsLength.trans ysLength.symm
  have packed : (xs = ys ↔ bytes1 = bytes2) := writeBytesInj be good words bytes1 bytes2 ⟨sameLength, capacity, wordCount⟩
  have magnitude : (mw2n xs = mw2n ys ↔ bytes1 = bytes2) := (mw2nInj xs ys lengths).trans packed
  have loop := wordCmpLoopThm xs ys frame1 frame2 a1 a2 domain memory
    ⟨lengths, by simpa [xsLength] using bound, first, second⟩
  have cmp := mwCmpThm xs ys lengths.symm
  by_cases equal : bytes1 = bytes2
  · have same := magnitude.mpr equal
    have result : mwCmp xs ys = none := by simpa [same] using cmp
    refine ⟨1, ?_, by simp [equal]⟩
    simpa [xsLength, result] using loop
  · have different : mw2n xs ≠ mw2n ys := fun h => equal (magnitude.mp h)
    by_cases less : mw2n xs < mw2n ys
    · have result : mwCmp xs ys = some true := by simpa [different, less] using cmp
      refine ⟨0, ?_, ?_⟩
      · simpa [xsLength, result] using loop
      · rcases good with h | h <;> subst width <;> simp [equal]
    · have result : mwCmp xs ys = some false := by simpa [different, less] using cmp
      refine ⟨2, ?_, ?_⟩
      · simpa [xsLength, result] using loop
      · rcases good with h | h <;> subst width <;> simp [equal]

/-- Equal content-comparison byte-array headers lead to a word loop whose
    equality result agrees with the source bytes. -/
theorem memoryRel_byteArraysEqualHeaderLoop {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (index1 index2 : Nat) (bytes1 bytes2 : List (BitVec 8)) (w1 w2 a1 a2 : BitVec width)
    (vars : List (DataSem.Value × WordLocW width))
    (rel : memoryRel conf be next refs space store memory domain
      ((.refPtr true index1, .word w1) :: (.refPtr true index2, .word w2) :: vars))
    (found1 : sptLookup index1 refs = some (.byteArray true bytes1))
    (found2 : sptLookup index2 refs = some (.byteArray true bytes2))
    (addr1 : getRealAddr conf store w1 = some a1) (addr2 : getRealAddr conf store w2 = some a2)
    (good : goodDimindex width)
    (sameHeader : DataToWord.makeByteHeader (width := width) conf true bytes1.length =
      DataToWord.makeByteHeader conf true bytes2.length) :
    ∃ result : BitVec width,
      wordCmpLoop (WordGcFunctions.decodeLength conf (DataToWord.makeByteHeader conf true bytes1.length))
        (a1 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf (DataToWord.makeByteHeader conf true bytes1.length))
        (a2 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf (DataToWord.makeByteHeader conf true bytes1.length))
        domain memory = some result ∧ (bytes1 = bytes2 ↔ result = 1) := by
  have tail := memoryRel_tail conf be next refs space store memory domain (.refPtr true index1, .word w1)
    ((.refPtr true index2, .word w2) :: vars) rel
  obtain ⟨p1, q1, loc1, _, real1, _, mem1, _, config, lenBound1⟩ :=
    memoryRel_byteArrayHeader conf be next refs space store memory domain true true index1 bytes1 (.word w1)
      ((.refPtr true index2, .word w2) :: vars) rel found1 good
  obtain ⟨p2, q2, loc2, _, real2, _, mem2, _, _, lenBound2⟩ :=
    memoryRel_byteArrayHeader conf be next refs space store memory domain true true index2 bytes2 (.word w2)
      vars tail found2 good
  have wp1 := WordLocW.word.inj loc1
  have wp2 := WordLocW.word.inj loc2
  subst p1
  subst p2
  have aq1 := Option.some.inj (real1.symm.trans addr1)
  have aq2 := Option.some.inj (real2.symm.trans addr2)
  subst q1
  subst q2
  have equalLengths := byteHeaderLengthInjective conf true true bytes1.length bytes2.length good config lenBound1 lenBound2 sameHeader
  obtain ⟨h1, frame1, actual1, words1, bound1, count1⟩ :=
    memoryRel_byteArrayWordsImp conf be next refs space store memory domain true true index1 bytes1 w1 a1
      ((.refPtr true index2, .word w2) :: vars) ⟨rel, found1, good, addr1⟩
  obtain ⟨h2, frame2, actual2, words2, bound2, count2⟩ :=
    memoryRel_byteArrayWordsImp conf be next refs space store memory domain true true index2 bytes2 w2 a2
      vars ⟨tail, found2, good, addr2⟩
  have hh1 := WordLocW.word.inj (actual1.symm.trans mem1)
  have hh2 := WordLocW.word.inj (actual2.symm.trans mem2)
  subst h1
  subst h2
  rw [← sameHeader] at words2 count2 bound2
  let count := (WordGcFunctions.decodeLength conf (DataToWord.makeByteHeader (width := width) conf true bytes1.length)).toNat
  let zeroWords : List (BitVec width) := List.replicate count 0
  have countEq : count = bytes1.length / (width / 8) + 1 := count1
  have cap : bytes1.length ≤ zeroWords.length * (width / 8) := by
    simp only [zeroWords, List.length_replicate, countEq]
    rcases good with hw | hw <;> subst width <;> norm_num <;> omega
  have countBound : zeroWords.length < 2 ^ width := by simpa [zeroWords, count] using bound1
  have countEnough : zeroWords.length ≤ bytes1.length / (width / 8) + 1 := by simp [zeroWords, countEq]
  obtain ⟨result, loop, correct⟩ := byteArrayWordEqualityLoop be zeroWords bytes1 bytes2 frame1 frame2
    a1 a2 domain memory good equalLengths cap countEnough countBound words1 words2
  refine ⟨result, ?_, correct⟩
  simpa [zeroWords, count] using loop

/-- Byte-array header bits identify whether equality compares the contents. -/
theorem byteHeaderContentBits {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (len : Nat) (flag : Bool) (good : goodDimindex width) (bound : conf.lenSize + 7 < width) :
    (DataToWord.makeByteHeader (width := width) conf flag len).getLsbD 2 = true ∧
    ((DataToWord.makeByteHeader (width := width) conf flag len).getLsbD 4 = false ↔ flag = true) := by
  rcases good with hw | hw <;> subst width
  · have h4 : ¬ (4 : Nat) ≥ 32 - 2 - conf.lenSize := by omega
    cases flag <;> simp [DataToWord.makeByteHeader, h4]
  · have h4 : ¬ (4 : Nat) ≥ 64 - 3 - conf.lenSize := by omega
    cases flag <;> simp [DataToWord.makeByteHeader, h4]

/-- A related comparison reference has the byte-content header exactly when
    its source cell is a content-comparing byte array. -/
theorem memoryRel_refPtrTrueContent {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (index : Nat) (w address header : BitVec width) (vars : List (DataSem.Value × WordLocW width))
    (rel : memoryRel conf be next refs space store memory domain ((.refPtr true index, .word w) :: vars))
    (real : getRealAddr conf store w = some address) (contents : memory address = .word header)
    (good : goodDimindex width) :
    (∃ bytes, sptLookup index refs = some (.byteArray true bytes)) ↔
      (header.getLsbD 2 = true ∧ header.getLsbD 4 = false) := by
  have noThunk : ∀ mode value, sptLookup index refs ≠ some (.thunk mode value) := by
    obtain ⟨heap, limit, a, sp, sp1, gens, _, wordInv, _, _⟩ := rel
    obtain ⟨roots, inv, _⟩ := wordInv
    obtain ⟨_, _, _, _, stackInv⟩ := inv
    obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
    cases roots with
    | nil => cases values
    | cons root rest =>
      cases values with
      | cons related _ =>
        exact ((valueInv_refPtr_true conf index refs root f tf heap).mp related).2.1
  obtain ⟨cell, found⟩ := memoryRel_refPtrExists conf be next refs space store memory domain true index (.word w) vars rel
  cases cell with
  | valueArray values =>
    obtain ⟨w', a', h', loc, _, _, bit2, _, _, addr, mem, _, _, _⟩ :=
      memoryRel_valueArrayImp conf be next refs space store memory domain true index values (.word w) vars ⟨rel, found, good⟩
    have weq := WordLocW.word.inj loc
    subst w'
    have aeq := Option.some.inj (addr.symm.trans real)
    subst a'
    have heq := WordLocW.word.inj (mem.symm.trans contents)
    subst h'
    simp [found, bit2]
  | byteArray flag bytes =>
    obtain ⟨w', a', loc, _, addr, _, mem, _, bound, _⟩ :=
      memoryRel_byteArrayHeader conf be next refs space store memory domain true flag index bytes (.word w) vars rel found good
    have weq := WordLocW.word.inj loc
    subst w'
    have aeq := Option.some.inj (addr.symm.trans real)
    subst a'
    have heq := WordLocW.word.inj (mem.symm.trans contents)
    subst header
    have bits := byteHeaderContentBits conf bytes.length flag good bound
    cases flag <;> simp_all
  | thunk mode value => exact False.elim (noThunk mode value found)
  | mutBlock tag finalised left child right =>
    exact False.elim (memoryRel_refPtrTrueNotMutBlock conf be next refs space store memory domain index (.word w) vars
      tag finalised left child right ⟨rel, found⟩)

/-- Successful true-valued reference equality either compares the same index
    or compares two identical byte arrays by content. -/
theorem vbEqSize_refTrue (refs : Spt (BvlSem.Ref DataSem.Value)) (i1 i2 n : Nat)
    (sized : vbEqSize refs (.refPtr true i1) (.refPtr true i2) = some (n, true)) :
    i1 = i2 ∨ ∃ bytes, sptLookup i1 refs = some (.byteArray true bytes) ∧
      sptLookup i2 refs = some (.byteArray true bytes) := by
  simp only [vbEqSize, Bool.true_and] at sized
  split at sized <;> simp_all
  all_goals split at sized <;> simp_all

/-- Every successful comparison of two comparison references uses one unit
    of source work. -/
theorem vbEqSize_refCount (refs : Spt (BvlSem.Ref DataSem.Value)) (i1 i2 n : Nat) (b : Bool)
    (sized : vbEqSize refs (.refPtr true i1) (.refPtr true i2) = some (n, b)) : n = 1 := by
  simp only [vbEqSize, Bool.true_and] at sized
  split at sized <;> simp_all
  all_goals split at sized <;> simp_all

/-- Without two content-comparing byte arrays, successful reference equality
    compares their source indices. -/
theorem vbEqSize_refNotBothContent (refs : Spt (BvlSem.Ref DataSem.Value)) (i1 i2 n : Nat) (b : Bool)
    (notBoth : ¬ ((∃ bytes, sptLookup i1 refs = some (.byteArray true bytes)) ∧
      (∃ bytes, sptLookup i2 refs = some (.byteArray true bytes))))
    (sized : vbEqSize refs (.refPtr true i1) (.refPtr true i2) = some (n, b)) : b = decide (i1 = i2) := by
  simp only [vbEqSize, Bool.true_and] at sized
  split at sized <;> simp_all
  all_goals split at sized <;> simp_all

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
