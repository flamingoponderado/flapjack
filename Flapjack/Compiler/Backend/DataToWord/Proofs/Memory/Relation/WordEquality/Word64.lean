import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueEquality
import Flapjack.Compiler.Backend.Semantics.DataSem.Stack

/-! Word64 case of the source word-equality simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- Reduce equality to the comparison loop for a matching word header (Flapjack helper). -/
private theorem eqStep {width : Nat} [NeZero width] (conf : DataToWord.Config)
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

/-- A one-word loop returns equality exactly for matching payloads (Flapjack helper). -/
private theorem loopOne {width : Nat} [NeZero width] (domain : BitVec width → Bool)
    (memory : BitVec width → WordLocW width) (a1 a2 x y : BitVec width)
    (good : goodDimindex width) (d1 : domain a1 = true) (d2 : domain a2 = true)
    (m1 : memory a1 = .word x) (m2 : memory a2 = .word y) :
    ∃ result, wordCmpLoop 1 a1 a2 domain memory = some result ∧ (result = 1 ↔ x = y) := by
  have oneNeZero : (1 : BitVec width) ≠ 0 := by rcases good with hw | hw <;> subst width <;> decide
  have zeroNeOne : (0 : BitVec width) ≠ 1 := Ne.symm oneNeZero
  have twoNeOne : (2 : BitVec width) ≠ 1 := by rcases good with hw | hw <;> subst width <;> decide
  by_cases eq : x = y
  · refine ⟨1, ?_, by simp [eq]⟩
    rw [wordCmpLoop]
    simp only [oneNeZero, ↓reduceIte, d1, d2, and_self, m1, m2, eq]
    rw [wordCmpLoop]
    simp
  · by_cases lt : x < y
    · refine ⟨0, ?_, ⟨fun h => (zeroNeOne h).elim, fun h => (eq h).elim⟩⟩
      rw [wordCmpLoop]
      simp only [oneNeZero, ↓reduceIte, d1, d2, and_self, m1, m2, eq, lt]
    · refine ⟨2, ?_, ⟨fun h => (twoNeOne h).elim, fun h => (eq h).elim⟩⟩
      rw [wordCmpLoop]
      simp only [oneNeZero, ↓reduceIte, d1, d2, and_self, m1, m2, eq, lt]

/-- A two-word loop returns equality exactly for matching payloads (Flapjack helper). -/
private theorem loopTwo {width : Nat} [NeZero width] (domain : BitVec width → Bool)
    (memory : BitVec width → WordLocW width) (a1 a2 x1 x2 y1 y2 : BitVec width)
    (good : goodDimindex width) (d1 : domain a1 = true) (d2 : domain a2 = true)
    (m1 : memory a1 = .word x2) (m2 : memory a2 = .word y2)
    (d1' : domain (a1 - StackRemove.bytesInWord width) = true)
    (d2' : domain (a2 - StackRemove.bytesInWord width) = true)
    (m1' : memory (a1 - StackRemove.bytesInWord width) = .word x1)
    (m2' : memory (a2 - StackRemove.bytesInWord width) = .word y1) :
    ∃ result, wordCmpLoop 2 a1 a2 domain memory = some result ∧
      (result = 1 ↔ x1 = y1 ∧ x2 = y2) := by
  have twoNeZero : (2 : BitVec width) ≠ 0 := by rcases good with hw | hw <;> subst width <;> decide
  have zeroNeOne : (0 : BitVec width) ≠ 1 := by rcases good with hw | hw <;> subst width <;> decide
  have twoNeOne : (2 : BitVec width) ≠ 1 := by rcases good with hw | hw <;> subst width <;> decide
  have sub : (2 : BitVec width) - 1 = 1 := by rcases good with hw | hw <;> subst width <;> decide
  by_cases eq : x2 = y2
  · obtain ⟨result, step, correct⟩ := loopOne domain memory _ _ x1 y1 good d1' d2' m1' m2'
    refine ⟨result, ?_, by simpa [eq] using correct⟩
    rw [wordCmpLoop]
    simpa only [twoNeZero, ↓reduceIte, d1, d2, and_self, m1, m2, eq, sub] using step
  · by_cases lt : x2 < y2
    · refine ⟨0, ?_, ?_⟩
      · rw [wordCmpLoop]
        simp only [twoNeZero, ↓reduceIte, d1, d2, and_self, m1, m2, eq, lt]
      · constructor
        · intro h; exact (zeroNeOne h).elim
        · rintro ⟨_, h⟩; exact (eq h).elim
    · refine ⟨2, ?_, ?_⟩
      · rw [wordCmpLoop]
        simp only [twoNeZero, ↓reduceIte, d1, d2, and_self, m1, m2, eq, lt]
      · constructor
        · intro h; exact (twoNeOne h).elim
        · rintro ⟨_, h⟩; exact (eq h).elim

/-- Word64 case of the source word-equality simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm0"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm0_word64 {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v1 v2 : BitVec 64) (limit clock : Nat) (b : Bool) (w1 w2 : BitVec width) (n : Nat)
    (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.word64 v1, .word w1) :: (.word64 v2, .word w2) :: vars) ∧
      vbEqSize refs (.word64 v1) (.word64 v2) = some (n, b) ∧
      clock = min (valueDepth (.word64 v1)) (valueDepth (.word64 v2)) ∧
      n * 2 ^ width < limit ∧ goodDimindex width →
    ∃ result remaining remainingClock, wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) ∧ limit ≤ remaining + n * 2 ^ width := by
  rintro ⟨rel, sized, ck, bound, good⟩
  simp only [vbEqSize, Option.some.injEq, Prod.mk.injEq] at sized
  obtain ⟨nEq, bEq⟩ := sized
  subst n
  subst b
  simp only [valueDepth, min_self] at ck
  subst clock
  simp only [Nat.one_mul] at bound
  by_cases eq : w1 = w2
  · subst w2
    have truth := memoryRel_ptrEq conf be next refs space store memory domain (.word64 v1) (.word64 v2)
      (.word w1) (decide (v1 = v2)) vars ⟨rel, by simp [doEq], good⟩
    refine ⟨1, limit, 0, ?_, ?_, by omega⟩
    · simp [wordEq]
    · simp [truth]
  · obtain ⟨ptr1, a1, h1, loc1, addr1, dom1, mem1, bit31, bit41, bit21, dom1', data1⟩ :=
      memoryRel_word64Imp conf be next refs space store memory domain v1 (.word w1)
        ((.word64 v2, .word w2) :: vars) ⟨rel, good⟩
    have tail := memoryRel_tail conf be next refs space store memory domain (.word64 v1, .word w1)
      ((.word64 v2, .word w2) :: vars) rel
    obtain ⟨ptr2, a2, h2, loc2, addr2, dom2, mem2, bit32, bit42, bit22, dom2', data2⟩ :=
      memoryRel_word64Imp conf be next refs space store memory domain v2 (.word w2) vars ⟨tail, good⟩
    have w1Eq := WordLocW.word.inj loc1
    have w2Eq := WordLocW.word.inj loc2
    have low1 : w1.getLsbD 0 = true := by rw [w1Eq]; exact getAddr_lowBit conf ptr1 _
    have low2 : w2.getLsbD 0 = true := by rw [w2Eq]; exact getAddr_lowBit conf ptr2 _
    have real1 : getRealAddr conf store w1 = some a1 := by simpa [w1Eq] using addr1
    have real2 : getRealAddr conf store w2 = some a2 := by simpa [w2Eq] using addr2
    rcases good with hw | hw <;> subst width
    · simp only [show 32 < 64 by decide, ↓reduceIte] at data1 data2
      obtain ⟨first1, dom1'', second1, len1, head1⟩ := data1
      obtain ⟨first2, dom2'', second2, len2, head2⟩ := data2
      have sameHeader : h1 = h2 := head1.trans head2.symm
      rw [← sameHeader] at mem2
      have mask : h1 &&& 12 ≠ 0 := by exact bitAnd12NeZero (by omega) h1 bit31
      have enough : (WordGcFunctions.decodeLength conf h1).toNat < limit := by rw [len1]; norm_num at bound ⊢; omega
      have position (a : BitVec 32) : a + StackRemove.bytesInWord 32 * (2 : BitVec 32) =
          a + (StackRemove.bytesInWord 32 <<< 1) := by
        congr 1
      have previous (a : BitVec 32) :
          (a + StackRemove.bytesInWord 32 * 2) - StackRemove.bytesInWord 32 =
            a + StackRemove.bytesInWord 32 := by bv_omega
      obtain ⟨result, loop, correct⟩ := loopTwo domain memory
        (a1 + StackRemove.bytesInWord 32 * 2) (a2 + StackRemove.bytesInWord 32 * 2)
        ((v1 >>> 32).setWidth 32) (v1.setWidth 32) ((v2 >>> 32).setWidth 32) (v2.setWidth 32)
        (Or.inl rfl) (by rw [position a1]; exact dom1'') (by rw [position a2]; exact dom2'')
        (by rw [position a1]; exact second1) (by rw [position a2]; exact second2)
        (by rw [previous a1]; exact dom1') (by rw [previous a2]; exact dom2')
        (by rw [previous a1]; exact first1) (by rw [previous a2]; exact first2)
      have loop' : wordCmpLoop (WordGcFunctions.decodeLength conf h1)
          (a1 + StackRemove.bytesInWord 32 * WordGcFunctions.decodeLength conf h1)
          (a2 + StackRemove.bytesInWord 32 * WordGcFunctions.decodeLength conf h1) domain memory = some result := by
        simpa [len1] using loop
      have eqParts : (((v1 >>> 32).setWidth 32 = (v2 >>> 32).setWidth 32) ∧
          v1.setWidth 32 = v2.setWidth 32) ↔ v1 = v2 := bitWord64Split v1 v2
      refine ⟨result, limit - 1 - (WordGcFunctions.decodeLength conf h1).toNat, 0, ?_, ?_, ?_⟩
      · exact eqStep conf store domain memory limit 0 w1 w2 a1 a2 h1 result eq low1 low2 real1 real2
          dom1 dom2 mem1 mem2 mask bit21 bit31 enough loop'
      · simpa only [decide_eq_true_eq] using eqParts.symm.trans correct.symm
      · rw [len1]
        norm_num at bound ⊢
        omega
    · simp only [show ¬ 64 < 64 by decide, ↓reduceIte] at data1 data2
      obtain ⟨first1, len1, head1⟩ := data1
      obtain ⟨first2, len2, head2⟩ := data2
      have sameHeader : h1 = h2 := head1.trans head2.symm
      rw [← sameHeader] at mem2
      have mask : h1 &&& 12 ≠ 0 := by exact bitAnd12NeZero (by omega) h1 bit31
      have enough : (WordGcFunctions.decodeLength conf h1).toNat < limit := by rw [len1]; norm_num at bound ⊢; omega
      obtain ⟨result, loop, correct⟩ := loopOne domain memory
        (a1 + StackRemove.bytesInWord 64) (a2 + StackRemove.bytesInWord 64) v1 v2
        (Or.inr rfl) dom1' dom2' (by simpa using first1) (by simpa using first2)
      have loop' : wordCmpLoop (WordGcFunctions.decodeLength conf h1)
          (a1 + StackRemove.bytesInWord 64 * WordGcFunctions.decodeLength conf h1)
          (a2 + StackRemove.bytesInWord 64 * WordGcFunctions.decodeLength conf h1) domain memory = some result := by
        simpa [len1] using loop
      refine ⟨result, limit - 1 - (WordGcFunctions.decodeLength conf h1).toNat, 0, ?_, ?_, ?_⟩
      · exact eqStep conf store domain memory limit 0 w1 w2 a1 a2 h1 result eq low1 low2 real1 real2
          dom1 dom2 mem1 mem2 mask bit21 bit31 enough loop'
      · simpa using correct.symm
      · rw [len1]
        norm_num at bound ⊢
        omega

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
