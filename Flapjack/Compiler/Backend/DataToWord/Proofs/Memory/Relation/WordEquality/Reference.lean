module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.ByteArray

@[expose] public section

/-! Reference case of the source word-equality simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- Reduce a content-comparing byte header to its word loop. -/
private theorem referenceEqStep {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (domain : BitVec width → Bool)
    (memory : BitVec width → WordLocW width) (limit clock : Nat) (w1 w2 a1 a2 h r : BitVec width)
    (diff : w1 ≠ w2) (low1 : w1.getLsbD 0 = true) (low2 : w2.getLsbD 0 = true)
    (addr1 : getRealAddr conf store w1 = some a1) (addr2 : getRealAddr conf store w2 = some a2)
    (dom1 : domain a1 = true) (dom2 : domain a2 = true)
    (mem1 : memory a1 = .word h) (mem2 : memory a2 = .word h)
    (mask : h &&& 12 ≠ 0) (bit2 : h.getLsbD 2 = true) (bit3 : h.getLsbD 3 = false)
    (bit4 : h.getLsbD 4 = false) (enough : (WordGcFunctions.decodeLength conf h).toNat < limit)
    (loop : wordCmpLoop (WordGcFunctions.decodeLength conf h)
      (a1 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h)
      (a2 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h) domain memory = some r) :
    wordEq conf store domain memory limit clock w1 w2 =
      some (r, limit - 1 - (WordGcFunctions.decodeLength conf h).toNat, clock) := by
  rw [wordEq]
  simp only [diff, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
  simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, bit2, bit3, bit4,
    show ¬ limit ≤ (WordGcFunctions.decodeLength conf h).toNat by omega, loop]
  intro zero
  exact False.elim (mask zero)

/-- The true/true reference case of the source equality simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm0"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm0_refPtrTrue {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (index1 index2 : Nat) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat)
    (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.refPtr true index1, .word w1) :: (.refPtr true index2, .word w2) :: vars) ∧
      vbEqSize refs (.refPtr true index1) (.refPtr true index2) = some (n, b) ∧
      clock = min (valueDepth (.refPtr true index1)) (valueDepth (.refPtr true index2)) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock, wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width := by
  rintro ⟨rel, sized, ck, bound, good⟩
  have count := vbEqSize_refCount refs index1 index2 n b sized
  subst n
  simp only [valueDepth, min_self] at ck
  subst clock
  simp only [Nat.one_mul] at bound
  obtain ⟨p1, p2, loc1, loc2, indexEq⟩ := memoryRel_refPtrEq conf be next refs space store memory domain
    index1 index2 (.word w1) (.word w2) vars ⟨rel, good⟩
  have wp1 := WordLocW.word.inj loc1
  have wp2 := WordLocW.word.inj loc2
  subst p1
  subst p2
  by_cases eq : w1 = w2
  · subst w2
    have erased := eraseValue refs (.refPtr true index1) (.refPtr true index2)
    rw [sized] at erased
    have doeq : doEq refs (.refPtr true index1) (.refPtr true index2) = .val b := by
      simpa [eraseCount] using erased.symm
    have truth := memoryRel_ptrEq conf be next refs space store memory domain
      (.refPtr true index1) (.refPtr true index2) (.word w1) b vars ⟨rel, doeq, good⟩
    refine ⟨1, limit, 0, ?_, ?_, by omega⟩
    · simp [wordEq]
    · simp [truth]
  · have indexNe : index1 ≠ index2 := fun h => eq (indexEq.mpr h)
    have tail := memoryRel_tail conf be next refs space store memory domain (.refPtr true index1, .word w1)
      ((.refPtr true index2, .word w2) :: vars) rel
    obtain ⟨p1, a1, h1, loc1, low1, bits1, addr1, _, mem1, dom1⟩ :=
      memoryRel_refPtrTrueImp conf be next refs space store memory domain index1 (.word w1)
        ((.refPtr true index2, .word w2) :: vars) ⟨rel, good⟩
    obtain ⟨p2, a2, h2, loc2, low2, bits2, addr2, _, mem2, dom2⟩ :=
      memoryRel_refPtrTrueImp conf be next refs space store memory domain index2 (.word w2) vars ⟨tail, good⟩
    have wp1 := WordLocW.word.inj loc1
    have wp2 := WordLocW.word.inj loc2
    subst p1
    subst p2
    have content1 := memoryRel_refPtrTrueContent conf be next refs space store memory domain index1 w1 a1 h1
      ((.refPtr true index2, .word w2) :: vars) rel addr1 mem1 good
    have content2 := memoryRel_refPtrTrueContent conf be next refs space store memory domain index2 w2 a2 h2
      vars tail addr2 mem2 good
    have mask : h1 &&& 12 ≠ 0 := by
      intro hz
      have widthBound : 3 < width := by rcases good with hw | hw <;> omega
      have bit := congrArg (fun y => y.getLsbD 2) hz
      have hb : (12 : BitVec width).getLsbD 2 = true := by
        rw [show (12 : BitVec width) = BitVec.ofNat width 12 from rfl, BitVec.getLsbD_ofNat]
        simp [show 2 < width by omega, show Nat.testBit 12 2 = true by decide]
      have hzbit : (0 : BitVec width).getLsbD 2 = false := by simp [BitVec.getLsbD]
      have h2 : h1.getLsbD 2 = false := by
        simpa only [BitVec.getLsbD_and, hb, Bool.and_true, hzbit] using bit
      have h3 := bits1.mpr h2
      exact bitAnd12NeZero widthBound h1 h3 hz
    by_cases both : (∃ bytes, sptLookup index1 refs = some (.byteArray true bytes)) ∧
        (∃ bytes, sptLookup index2 refs = some (.byteArray true bytes))
    · obtain ⟨⟨bytes1, found1⟩, ⟨bytes2, found2⟩⟩ := both
      have bEq : b = decide (bytes1 = bytes2) := by
        simpa [vbEqSize, found1, found2] using sized.symm
      obtain ⟨p1, q1, loc1, _, real1, _, header1, _, _, _⟩ :=
        memoryRel_byteArrayHeader conf be next refs space store memory domain true true index1 bytes1 (.word w1)
          ((.refPtr true index2, .word w2) :: vars) rel found1 good
      obtain ⟨p2, q2, loc2, _, real2, _, header2, _, _, _⟩ :=
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
      have hh1 := WordLocW.word.inj (mem1.symm.trans header1)
      have hh2 := WordLocW.word.inj (mem2.symm.trans header2)
      by_cases headerEq : h1 = h2
      · have sameHeader := hh1.symm.trans (headerEq.trans hh2)
        have bits := content1.mp ⟨bytes1, found1⟩
        have bit3 : h1.getLsbD 3 = false := by
          cases h : h1.getLsbD 3 with
          | false => rfl
          | true =>
            have impossible := bits1.mp h
            rw [bits.1] at impossible
            contradiction
        obtain ⟨result, loop, correct⟩ := memoryRel_byteArraysEqualHeaderLoop conf be next refs space store memory domain
          index1 index2 bytes1 bytes2 w1 w2 a1 a2 vars rel found1 found2 addr1 addr2 good sameHeader
        obtain ⟨h, frame, actual, _, countBound, _⟩ :=
          memoryRel_byteArrayWordsImp conf be next refs space store memory domain true true index1 bytes1 w1 a1
            ((.refPtr true index2, .word w2) :: vars) ⟨rel, found1, good, addr1⟩
        have heq := WordLocW.word.inj (actual.symm.trans mem1)
        subst h
        have enough : (WordGcFunctions.decodeLength conf h1).toNat < limit := by omega
        have loop' : wordCmpLoop (WordGcFunctions.decodeLength conf h1)
            (a1 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h1)
            (a2 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h1) domain memory = some result := by
          simpa only [hh1] using loop
        rw [← headerEq] at mem2
        refine ⟨result, limit - 1 - (WordGcFunctions.decodeLength conf h1).toNat, 0, ?_, ?_, ?_⟩
        · exact referenceEqStep conf store domain memory limit 0 w1 w2 a1 a2 h1 result eq low1 low2 addr1 addr2
            dom1 dom2 mem1 mem2 mask bits.1 bit3 bits.2 enough loop'
        · simpa [bEq] using correct
        · omega
      · have different : bytes1 ≠ bytes2 := by
          intro same
          subst bytes2
          exact headerEq (hh1.trans hh2.symm)
        have bf : b = false := by simp [bEq, different]
        subst b
        refine ⟨0, limit, 0, ?_, ?_, by omega⟩
        · rw [wordEq]
          simp only [eq, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
          simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, headerEq]
          intro zero _
          exact (mask zero).elim
        · rcases good with hw | hw <;> subst width <;> simp [different]
    · have bEq := vbEqSize_refNotBothContent refs index1 index2 1 b both sized
      have bf : b = false := by simp [bEq, indexNe]
      subst b
      refine ⟨0, limit, 0, ?_, ?_, by omega⟩
      · by_cases headerEq : h1 = h2
        · have noContent1 : ¬ ∃ bytes, sptLookup index1 refs = some (.byteArray true bytes) := by
            intro exists1
            apply both
            refine ⟨exists1, content2.mpr ?_⟩
            rw [← headerEq]
            exact content1.mp exists1
          have noBits : ¬ (h1.getLsbD 2 = true ∧ h1.getLsbD 4 = false) :=
            fun h => noContent1 (content1.mpr h)
          rw [← headerEq] at mem2
          by_cases bit2 : h1.getLsbD 2 = true
          · have bit4 : h1.getLsbD 4 = true := by
              cases h : h1.getLsbD 4 with
              | false => exact (noBits ⟨bit2, h⟩).elim
              | true => rfl
            have bit3 : h1.getLsbD 3 = false := by
              cases h : h1.getLsbD 3 with
              | false => rfl
              | true =>
                have impossible := bits1.mp h
                rw [bit2] at impossible
                contradiction
            rw [wordEq]
            simp only [eq, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
            simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, bit2, bit3, bit4]
            intro zero
            exact (mask zero).elim
          · have bit2false : h1.getLsbD 2 = false := by cases h : h1.getLsbD 2 <;> simp_all
            rw [wordEq]
            simp only [eq, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
            simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, bit2false]
            intro zero
            exact (mask zero).elim
        · rw [wordEq]
          simp only [eq, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
          simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, headerEq]
          intro zero _
          exact (mask zero).elim
      · rcases good with hw | hw <;> subst width <;> simp [indexNe]

/-- The false/any reference case is impossible because source equality fails. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm0"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm0_refPtrFalseLeft {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (flag : Bool) (index1 index2 : Nat) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat)
    (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.refPtr false index1, .word w1) :: (.refPtr flag index2, .word w2) :: vars) ∧
      vbEqSize refs (.refPtr false index1) (.refPtr flag index2) = some (n, b) ∧
      clock = min (valueDepth (.refPtr false index1)) (valueDepth (.refPtr flag index2)) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock, wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width := by
  rintro ⟨_, sized, _, _, _⟩
  cases flag <;> simp [vbEqSize] at sized

/-- The true/false reference case is impossible because source equality fails. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm0"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm0_refPtrFalseRight {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (index1 index2 : Nat) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat)
    (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.refPtr true index1, .word w1) :: (.refPtr false index2, .word w2) :: vars) ∧
      vbEqSize refs (.refPtr true index1) (.refPtr false index2) = some (n, b) ∧
      clock = min (valueDepth (.refPtr true index1)) (valueDepth (.refPtr false index2)) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock, wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width := by
  rintro ⟨_, sized, _, _, _⟩
  simp [vbEqSize] at sized

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
