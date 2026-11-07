import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BignumCompare
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.Word64

/-! Number case of the source word-equality simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Misc.Multiword
open Classical
noncomputable section

/-- Reduce equal numeric headers to their payload comparison loop. -/
private theorem numberEqStep {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (domain : BitVec width → Bool)
    (memory : BitVec width → WordLocW width) (limit clock : Nat) (w1 w2 a1 a2 h r : BitVec width)
    (diff : w1 ≠ w2) (low1 : w1.getLsbD 0 = true) (low2 : w2.getLsbD 0 = true)
    (addr1 : getRealAddr conf store w1 = some a1) (addr2 : getRealAddr conf store w2 = some a2)
    (dom1 : domain a1 = true) (dom2 : domain a2 = true)
    (mem1 : memory a1 = .word h) (mem2 : memory a2 = .word h)
    (mask : h &&& 12 ≠ 0) (bit2 : h.getLsbD 2 = true) (bit3 : h.getLsbD 3 = true)
    (enough : (WordGcFunctions.decodeLength conf h).toNat < limit)
    (loop : wordCmpLoop (WordGcFunctions.decodeLength conf h)
      (a1 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h)
      (a2 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h) domain memory = some r) :
    wordEq conf store domain memory limit clock w1 w2 =
      some (r, limit - 1 - (WordGcFunctions.decodeLength conf h).toNat, clock) := by
  rw [wordEq]
  simp only [diff, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
  simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, bit2, bit3,
    show ¬ limit ≤ (WordGcFunctions.decodeLength conf h).toNat by omega, loop]
  intro zero
  exact False.elim (mask zero)

/-- Distinct related numeric words cannot encode equal integers when at
    least one is immediate. -/
private theorem differentImmediateNumbers {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (w1 w2 : BitVec width) (vars : List (Value × WordLocW width))
    (rel : memoryRel conf be next refs space store memory domain ((.number i1, .word w1) :: (.number i2, .word w2) :: vars))
    (good : goodDimindex width) (different : w1 ≠ w2) (small : smallInt width i1 ∨ smallInt width i2) :
    i1 ≠ i2 := by
  obtain ⟨q1, q2, h1, h2, same⟩ := memoryRel_numberEq conf be next refs space store memory domain
    i1 i2 (.word w1) (.word w2) vars ⟨rel, small, good⟩
  have e1 := WordLocW.word.inj h1
  have e2 := WordLocW.word.inj h2
  intro equal
  apply different
  exact e1.trans ((same.mpr equal).trans e2.symm)

/-- Number case of the source word-equality simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm0"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm0_number {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat)
    (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.number i1, .word w1) :: (.number i2, .word w2) :: vars) ∧
      vbEqSize refs (.number i1) (.number i2) = some (n, b) ∧
      clock = min (valueDepth (.number i1)) (valueDepth (.number i2)) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock, wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width := by
  rintro ⟨rel, sized, ck, bound, good⟩
  simp only [vbEqSize, Option.some.injEq, Prod.mk.injEq] at sized
  obtain ⟨rfl, rfl⟩ := sized
  simp only [valueDepth, min_self] at ck
  subst clock
  simp only [Nat.one_mul] at bound
  by_cases eq : w1 = w2
  · subst w2
    have truth := memoryRel_ptrEq conf be next refs space store memory domain (.number i1) (.number i2)
      (.word w1) (decide (i1 = i2)) vars ⟨rel, by simp [doEq], good⟩
    refine ⟨1, limit, 0, ?_, ?_, by omega⟩
    · simp [wordEq]
    · simp [truth]
  · by_cases low1 : w1.getLsbD 0 = true
    · by_cases low2 : w2.getLsbD 0 = true
      · have tail := memoryRel_tail conf be next refs space store memory domain (.number i1, .word w1)
          ((.number i2, .word w2) :: vars) rel
        obtain ⟨p1, loc1, bit1⟩ := memoryRel_anyNumberImp conf be next refs space store memory domain
          i1 (.word w1) ((.number i2, .word w2) :: vars) ⟨good, rel⟩
        obtain ⟨p2, loc2, bit2⟩ := memoryRel_anyNumberImp conf be next refs space store memory domain
          i2 (.word w2) vars ⟨good, tail⟩
        have wp1 := WordLocW.word.inj loc1
        have wp2 := WordLocW.word.inj loc2
        subst p1
        subst p2
        have large1 : ¬ smallInt width i1 := bit1.mp low1
        have large2 : ¬ smallInt width i2 := bit2.mp low2
        obtain ⟨p1, a1, f1, loc1, addr1, mem1, dom1, words1, bound1, _, h12, h13, sign1, decoded1⟩ :=
          memoryRel_bignumWords conf be next refs space store memory domain i1 (.word w1)
            ((.number i2, .word w2) :: vars) ⟨rel, large1, good⟩
        obtain ⟨p2, a2, f2, loc2, addr2, mem2, dom2, words2, bound2, _, _, _, sign2, decoded2⟩ :=
          memoryRel_bignumWords conf be next refs space store memory domain i2 (.word w2) vars ⟨tail, large2, good⟩
        have wp1 := WordLocW.word.inj loc1
        have wp2 := WordLocW.word.inj loc2
        subst p1
        subst p2
        let h1 : BitVec width := makeHeader conf (((if i1 < 0 then 1 else 0) <<< 2) ||| 3)
          (n2mw i1.natAbs : List (BitVec width)).length
        let h2 : BitVec width := makeHeader conf (((if i2 < 0 then 1 else 0) <<< 2) ||| 3)
          (n2mw i2.natAbs : List (BitVec width)).length
        change memory a1 = .word h1 at mem1
        change memory a2 = .word h2 at mem2
        change h1.getLsbD 2 = true at h12
        change h1.getLsbD 3 = true at h13
        change (h1.getLsbD 4 = true ↔ i1 < 0) at sign1
        change (h2.getLsbD 4 = true ↔ i2 < 0) at sign2
        change WordGcFunctions.decodeLength conf h1 = BitVec.ofNat width (n2mw i1.natAbs : List (BitVec width)).length at decoded1
        change WordGcFunctions.decodeLength conf h2 = BitVec.ofNat width (n2mw i2.natAbs : List (BitVec width)).length at decoded2
        have mask : h1 &&& 12 ≠ 0 := bitAnd12NeZero (by rcases good with hw | hw <;> omega) h1 h13
        have power : 2 ^ (width - 4) ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
        have small1 : (n2mw i1.natAbs : List (BitVec width)).length < 2 ^ width := lt_of_lt_of_le bound1 power
        have small2 : (n2mw i2.natAbs : List (BitVec width)).length < 2 ^ width := lt_of_lt_of_le bound2 power
        by_cases headerEq : h1 = h2
        · have sameSign : (i1 < 0 ↔ i2 < 0) := by rw [← sign1, ← sign2, headerEq]
          have sameDecoded := decoded1.symm.trans (headerEq ▸ decoded2)
          have sameLength : (n2mw i1.natAbs : List (BitVec width)).length =
              (n2mw i2.natAbs : List (BitVec width)).length := by
            have h := congrArg BitVec.toNat sameDecoded
            simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small1, Nat.mod_eq_of_lt small2] using h
          obtain ⟨result, loop, correct⟩ := bignumWordEqualityLoop i1 i2 f1 f2 a1 a2 domain memory
            good sameSign sameLength small1 words1 words2
          have enough : (WordGcFunctions.decodeLength conf h1).toNat < limit := by
            rw [decoded1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small1]
            omega
          have loop' : wordCmpLoop (WordGcFunctions.decodeLength conf h1)
              (a1 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h1)
              (a2 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h1) domain memory = some result := by
            simpa only [decoded1] using loop
          rw [← headerEq] at mem2
          refine ⟨result, limit - 1 - (WordGcFunctions.decodeLength conf h1).toNat, 0, ?_, ?_, ?_⟩
          · exact numberEqStep conf store domain memory limit 0 w1 w2 a1 a2 h1 result eq low1 low2 addr1 addr2
              dom1 dom2 mem1 mem2 mask h12 h13 enough loop'
          · simpa using correct
          · rw [decoded1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small1]
            omega
        · have unequal : i1 ≠ i2 := by
            intro same
            subst i2
            exact headerEq rfl
          refine ⟨0, limit, 0, ?_, ?_, by omega⟩
          · rw [wordEq]
            simp only [eq, ↓reduceIte, low1, low2, Bool.true_and, Bool.not_true, Bool.false_eq_true]
            simp [wordHeader, addr1, addr2, dom1, dom2, mem1, mem2, headerEq]
            intro zero _
            exact (mask zero).elim
          · rcases good with hw | hw <;> subst width <;> simp [unequal]
      · have tail := memoryRel_tail conf be next refs space store memory domain (.number i1, .word w1)
          ((.number i2, .word w2) :: vars) rel
        obtain ⟨p, loc, bit⟩ := memoryRel_anyNumberImp conf be next refs space store memory domain
          i2 (.word w2) vars ⟨good, tail⟩
        have eqp := WordLocW.word.inj loc
        subst p
        have small2 : smallInt width i2 := by
          by_contra large
          exact low2 (bit.mpr large)
        have unequal := differentImmediateNumbers conf be next refs space store memory domain i1 i2 w1 w2 vars
          rel good eq (Or.inr small2)
        have clear2 : w2.getLsbD 0 = false := by cases h : w2.getLsbD 0 <;> simp_all
        refine ⟨0, limit, 0, ?_, ?_, by omega⟩
        · simp [wordEq, eq, clear2]
        · rcases good with hw | hw <;> subst width <;> simp [unequal]
    · obtain ⟨p, loc, bit⟩ := memoryRel_anyNumberImp conf be next refs space store memory domain
        i1 (.word w1) ((.number i2, .word w2) :: vars) ⟨good, rel⟩
      have eqp := WordLocW.word.inj loc
      subst p
      have small1 : smallInt width i1 := by
        by_contra large
        exact low1 (bit.mpr large)
      have unequal := differentImmediateNumbers conf be next refs space store memory domain i1 i2 w1 w2 vars
        rel good eq (Or.inl small1)
      have clear1 : w1.getLsbD 0 = false := by cases h : w1.getLsbD 0 <;> simp_all
      refine ⟨0, limit, 0, ?_, ?_, by omega⟩
      · simp [wordEq, eq, clear1]
      · rcases good with hw | hw <;> subst width <;> simp [unequal]

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
