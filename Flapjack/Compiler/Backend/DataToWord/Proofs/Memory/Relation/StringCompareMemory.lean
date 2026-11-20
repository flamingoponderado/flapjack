module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StringCompare
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArrayImp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.WordGcFunctions Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Comparing two related byte arrays agrees with the source string comparison.
The two unused HOL existential witnesses are omitted; neither occurs in the conclusion. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_str_cmp"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRelStrCmp {width : Nat} [NeZero width]
    (c : Config) (be : Bool) (ts : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (bl1 bl2 : Bool) (p1 p2 : Nat) (v1 v2 : WordLocW width)
    (vars : List (DataSem.Value × WordLocW width)) (fl1 fl2 : Bool) (vals1 vals2 : List (BitVec 8))
    (b : Bool) (cmp : Flapjack.Opb)
    (rel : memoryRel c be ts refs sp st m dm ((.refPtr bl1 p1,v1)::(.refPtr bl2 p2,v2)::vars))
    (found1 : sptLookup p1 refs = some (.byteArray fl1 vals1))
    (found2 : sptLookup p2 refs = some (.byteArray fl2 vals2)) (good : goodDimindex width) :
    ∃ w1 a1 w2 a2 r1 r2,
      v1 = .word w1 ∧ v2 = .word w2 ∧ getRealAddr c st w1 = some a1 ∧
      getRealAddr c st w2 = some a2 ∧ wordStrCmp b a1 a2 dm m be c = some (r1,r2) ∧
      (strCmp b cmp (.implode (vals1.map (fun x => BitVec.ofNat 8 x.toNat)))
         (.implode (vals2.map (fun x => BitVec.ofNat 8 x.toNat))) = true ↔
       numCmp cmp r1.toNat r2.toNat = true) := by
  have tailRel := memoryRel_tl c be ts refs sp st m dm (.refPtr bl1 p1,v1) ((.refPtr bl2 p2,v2)::vars) rel
  obtain ⟨w1, a1, header1, loc1, bit1, hd1, _, _, _, simple1, real1, mem1, dom1, reads1, updates1, bounds1⟩ :=
    memoryRel_byteArrayImp c be ts refs sp st m dm bl1 fl1 p1 vals1 v1 ((.refPtr bl2 p2,v2)::vars) ⟨rel, found1, good⟩
  obtain ⟨w2, a2, header2, loc2, bit2, hd2, _, _, _, simple2, real2, mem2, dom2, reads2, updates2, bounds2⟩ :=
    memoryRel_byteArrayImp c be ts refs sp st m dm bl2 fl2 p2 vals2 v2 vars ⟨tailRel, found2, good⟩
  subst header1
  subst header2
  have shift1 : (makeByteHeader c fl1 vals1.length : BitVec width) >>> (width - c.lenSize - wordShiftAmount width) =
      BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width) := by
    rcases good with hw | hw <;> subst width <;> simp [wordShiftAmount] at bounds1 ⊢ <;> exact bounds1.2
  have shift2 : (makeByteHeader c fl2 vals2.length : BitVec width) >>> (width - c.lenSize - wordShiftAmount width) =
      BitVec.ofNat width (vals2.length + 2 ^ wordShiftAmount width) := by
    rcases good with hw | hw <;> subst width <;> simp [wordShiftAmount] at bounds2 ⊢ <;> exact bounds2.2
  have len1 : vals1.length + 2 ^ wordShiftAmount width < 2 ^ width := by
    rcases good with hw | hw <;> subst width <;> simp [wordShiftAmount] at bounds1 ⊢ <;> omega
  have len2 : vals2.length + 2 ^ wordShiftAmount width < 2 ^ width := by
    rcases good with hw | hw <;> subst width <;> simp [wordShiftAmount] at bounds2 ⊢ <;> omega
  have read1 : ∀ i (h : i < vals1.length), memLoadByteAuxExact m dm be (a1 + wordSemBytesInWord + BitVec.ofNat width i) = some vals1[i] := by
    simpa [wordSemBytesInWord, StackRemove.bytesInWord] using reads1
  have read2 : ∀ i (h : i < vals2.length), memLoadByteAuxExact m dm be (a2 + wordSemBytesInWord + BitVec.ofNat width i) = some vals2[i] := by
    simpa [wordSemBytesInWord, StackRemove.bytesInWord] using reads2
  have stride : (wordSemBytesInWord : BitVec width) = BitVec.ofNat width (2 ^ wordShiftAmount width) := by
    rcases good with hw | hw <;> subst width <;> rfl
  cases b with
  | false =>
    obtain ⟨r1,r2,diff,comparison⟩ := findDiffStrCmpThm2 (width := width) 0 vals1 vals2
      (vals1.length + 2 ^ wordShiftAmount width) (vals2.length + 2 ^ wordShiftAmount width) cmp
      rfl rfl (by simpa using len1) (by simpa using len2) good
    have nbound : min vals1.length vals2.length < 2 ^ width := by
      have hlen : vals1.length < 2 ^ width := lt_of_le_of_lt (Nat.le_add_right _ _) len1
      exact lt_of_le_of_lt (Nat.min_le_left _ _) hlen
    have loop := wordStrLoopThm (min vals1.length vals2.length) (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord)
      (BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width))
      (BitVec.ofNat width (vals2.length + 2 ^ wordShiftAmount width)) dm m be (2 ^ width) vals1 vals2
      read1 read2 (Nat.min_le_left _ _) (Nat.min_le_right _ _) nbound (by rfl)
    simp only [Nat.zero_add] at diff
    rw [diff] at loop
    have minWord : (BitVec.ofNat width (min vals1.length vals2.length) + wordSemBytesInWord : BitVec width) =
        BitVec.ofNat width (min (vals1.length + 2 ^ wordShiftAmount width) (vals2.length + 2 ^ wordShiftAmount width)) := by
      rw [Nat.add_min_add_right, BitVec.ofNat_add, stride]
    have count1 : (BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width)).toNat = vals1.length + 2 ^ wordShiftAmount width := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt len1]
    have count2 : (BitVec.ofNat width (vals2.length + 2 ^ wordShiftAmount width)).toNat = vals2.length + 2 ^ wordShiftAmount width := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt len2]
    refine ⟨w1,a1,w2,a2,r1,r2,loc1,loc2,real1,real2,?_,comparison⟩
    simp only [wordStrCmp, dom1, dom2, Bool.true_and, mem1, mem2, wordSemIsWordLoc, wordSemTheWord,
      Bool.false_eq_true, ↓reduceIte, shift1, shift2, count1, count2]
    simpa only [minWord] using loop
  | true =>
    by_cases eqLen : vals1.length = vals2.length
    · obtain ⟨r1,r2,diff,comparison⟩ := findDiffStrCmpThm1 (width := width) vals1 vals2
        (vals1.length + 2 ^ wordShiftAmount width) cmp eqLen good
      have nbound : vals1.length < 2 ^ width := lt_of_le_of_lt (Nat.le_add_right _ _) len1
      have loop := wordStrLoopThm vals1.length (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord)
        (BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width))
        (BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width)) dm m be (2 ^ width) vals1 vals2
        read1 read2 (by rfl) (by simp [eqLen]) nbound (by rfl)
      have take2 : vals2.take vals1.length = vals2 := by rw [eqLen]; exact List.take_length
      rw [List.take_length, take2, diff] at loop
      have lenWord : (BitVec.ofNat width vals1.length + wordSemBytesInWord : BitVec width) =
          BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width) := by
        rw [BitVec.ofNat_add, stride]
      have shift2eq : (makeByteHeader c fl2 vals1.length : BitVec width) >>>
          (width - c.lenSize - wordShiftAmount width) =
          BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width) := by
        simpa only [eqLen] using shift2
      refine ⟨w1,a1,w2,a2,r1,r2,loc1,loc2,real1,real2,?_,comparison⟩
      simp only [wordStrCmp, dom1, dom2, Bool.true_and, mem1, mem2, wordSemIsWordLoc, wordSemTheWord,
        ↓reduceIte, shift1, ← eqLen]
      simp only [shift2eq, ne_eq, not_true_eq_false, ↓reduceIte]
      simpa only [lenWord] using loop
    · have hwordNe : (BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width) : BitVec width) ≠
          BitVec.ofNat width (vals2.length + 2 ^ wordShiftAmount width) := by
        intro heq
        have hn := congrArg BitVec.toNat heq
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt len1, Nat.mod_eq_of_lt len2] at hn
        exact eqLen hn
      have count1 : (BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width)).toNat = vals1.length + 2 ^ wordShiftAmount width := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt len1]
      have count2 : (BitVec.ofNat width (vals2.length + 2 ^ wordShiftAmount width)).toNat = vals2.length + 2 ^ wordShiftAmount width := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt len2]
      have orderEq : compare vals1.length vals2.length =
          compare (vals1.length + 2 ^ wordShiftAmount width) (vals2.length + 2 ^ wordShiftAmount width) := by
        simp [compare, compareOfLessAndEq]
      have comparison : strCmp true cmp (.implode (vals1.map (fun x => BitVec.ofNat 8 x.toNat)))
           (.implode (vals2.map (fun x => BitVec.ofNat 8 x.toNat))) = true ↔
          numCmp cmp (vals1.length + 2 ^ wordShiftAmount width) (vals2.length + 2 ^ wordShiftAmount width) = true := by
        simp [strCmp, numCmp, MlString.explode, eqLen, orderEq]
      refine ⟨w1,a1,w2,a2,
        BitVec.ofNat width (vals1.length + 2 ^ wordShiftAmount width),
        BitVec.ofNat width (vals2.length + 2 ^ wordShiftAmount width),loc1,loc2,real1,real2,?_,?_⟩
      · simp only [wordStrCmp, dom1, dom2, Bool.true_and, mem1, mem2, wordSemIsWordLoc, wordSemTheWord,
          ↓reduceIte, shift1, shift2]
        simp only [if_pos hwordNe]
      · simpa only [count1,count2] using comparison

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
