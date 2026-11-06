import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockEquality
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefEquality
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare

/-! Cases of pointer equality for the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The block/block case of pointer equality, using the structural induction
hypothesis for each child of the first block. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_pointer_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_pointerEq_blockBlock {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (ts1 tag1 ts2 tag2 : Nat) (vals1 vals2 : List Value) (location : WordLocW width) (b : Bool)
    (vars : List (Value × WordLocW width))
    (ih : ∀ child ∈ vals1, ∀ other loc result tail,
      memoryRel conf bigEndian next refs space store memory domain ((child, loc) :: (other, loc) :: tail) ∧
      goodDimindex width ∧ doEq refs child other = .val result →
      result = true)
    (h : memoryRel conf bigEndian next refs space store memory domain
        ((.block ts1 tag1 vals1, location) :: (.block ts2 tag2 vals2, location) :: vars) ∧
      goodDimindex width ∧ doEq refs (.block ts1 tag1 vals1) (.block ts2 tag2 vals2) = .val b) : b = true := by
  obtain ⟨inv, good, compare⟩ := h
  obtain ⟨w, locationEq, _⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
    ts1 tag1 vals1 location ((.block ts2 tag2 vals2, location) :: vars) ⟨inv, good⟩
  subst location
  obtain ⟨tags, lengths⟩ := memoryRel_blocksSameWord conf bigEndian next refs space store memory domain
    ts1 tag1 ts2 tag2 vals1 vals2 w vars inv good
  subst tag2
  cases b with
  | true => rfl
  | false =>
    have listEq : doEqList refs vals1 vals2 = .val false := by
      by_cases clos1 : isClosure tag1 vals1 <;> by_cases clos2 : isClosure tag1 vals2 <;>
        simp [doEq, clos1, clos2, lengths] at compare
      exact compare
    obtain ⟨i, hi1, hi2, different⟩ := doEqList_falseElement refs vals1 vals2 ⟨listEq, lengths.symm⟩
    obtain ⟨w1, addr1, _, loc1, real1, _, inv1⟩ :=
      memoryRel_elAny conf bigEndian next refs space store memory domain ts1 tag1 vals1 (.word w)
        ((.block ts2 tag1 vals2, .word w) :: vars) i hi1 ⟨inv, good⟩
    have sameW1 : w = w1 := WordLocW.word.inj loc1
    subst w1
    let cell1 := memory (addr1 + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i)
    have swapped : memoryRel conf bigEndian next refs space store memory domain
        ((.block ts2 tag1 vals2, .word w) :: (vals1[i], cell1) :: (.block ts1 tag1 vals1, .word w) :: vars) := by
      apply memoryRel_rearrange conf bigEndian next refs space store memory domain _ _ ?_ inv1
      intro pair member
      simp only [List.mem_cons] at member ⊢
      aesop
    obtain ⟨w2, addr2, _, loc2, real2, _, inv2⟩ :=
      memoryRel_elAny conf bigEndian next refs space store memory domain ts2 tag1 vals2 (.word w)
        ((vals1[i], cell1) :: (.block ts1 tag1 vals1, .word w) :: vars) i hi2 ⟨swapped, good⟩
    have sameW2 : w = w2 := WordLocW.word.inj loc2
    subst w2
    have sameAddr : addr1 = addr2 := Option.some.inj (real1.symm.trans real2)
    subst addr2
    have children : memoryRel conf bigEndian next refs space store memory domain
        ((vals1[i], cell1) :: (vals2[i], cell1) :: []) := by
      apply memoryRel_rearrange conf bigEndian next refs space store memory domain _ _ ?_ inv2
      intro pair member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      dsimp [cell1] at member ⊢
      aesop
    have impossible := ih vals1[i] (List.getElem_mem hi1) vals2[i] cell1 false [] ⟨children, good, different⟩
    contradiction

/-- The reference-pointer/reference-pointer case of pointer equality. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_pointer_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_pointerEq_refRef {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (compare1 compare2 : Bool) (i1 i2 : Nat) (location : WordLocW width) (b : Bool)
    (vars : List (Value × WordLocW width))
    (h : memoryRel conf bigEndian next refs space store memory domain
        ((.refPtr compare1 i1, location) :: (.refPtr compare2 i2, location) :: vars) ∧
      goodDimindex width ∧ doEq refs (.refPtr compare1 i1) (.refPtr compare2 i2) = .val b) : b = true := by
  obtain ⟨inv, good, compare⟩ := h
  cases compare1 <;> cases compare2 <;> simp [doEq] at compare
  obtain ⟨w1, w2, eq1, eq2, same⟩ := memoryRel_refPtrEq conf bigEndian next refs space store memory domain
    i1 i2 location location vars ⟨inv, good⟩
  have sameWord : w1 = w2 := WordLocW.word.inj (eq1.symm.trans eq2)
  have sameIndex : i1 = i2 := same.mp sameWord
  subst i2
  cases lookup : sptLookup i1 refs with
  | none => simpa [lookup] using compare.symm
  | some cell =>
    cases cell <;> simp_all
    case byteArray flag bytes => cases flag <;> simp_all

/-- For supported target widths, the abstract word64 payload determines its
64-bit input. This Flapjack bit-vector helper is used by pointer equality. -/
theorem word64Rep_injective {width : Nat} [NeZero width] (good : goodDimindex width) (w1 w2 : BitVec 64)
    (same : (word64Rep (width := width) (α := WordLocW width) w1) = word64Rep w2) : w1 = w2 := by
  rcases good with width32 | width64 <;> subst width
  · simp [word64Rep] at same
    exact (bitWord64Split w1 w2).mp same
  · simp [word64Rep] at same
    exact same

/-- The word64/word64 case of the pointer-equality theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_pointer_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_pointerEq_word64Word64 {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (word1 word2 : BitVec 64) (location : WordLocW width) (b : Bool)
    (vars : List (Value × WordLocW width))
    (h : memoryRel conf bigEndian next refs space store memory domain
        ((.word64 word1, location) :: (.word64 word2, location) :: vars) ∧
      goodDimindex width ∧ doEq refs (.word64 word1) (.word64 word2) = .val b) : b = true := by
  obtain ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩, good, compare⟩ := h
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := absInv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root1 rest =>
    cases rest with
    | nil => cases values with | cons _ tail => cases tail
    | cons root2 rest =>
      cases values with
      | cons first more =>
        cases more with
        | cons second _ =>
          cases addresses with
          | cons addr1 more =>
            cases more with
            | cons addr2 _ =>
              obtain ⟨ptr1, rootEq1, found1⟩ := (valueInv_word64 conf word1 refs root1 f tf heap).mp first
              obtain ⟨ptr2, rootEq2, found2⟩ := (valueInv_word64 conf word2 refs root2 f tf heap).mp second
              subst root1
              subst root2
              have heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf := heapMem.1
              have ptrBound : ∀ ptr word, heapLookup ptr heap = some (word64Rep word) →
                  ptr * 2 ^ shiftLength conf < 2 ^ width := by
                intro ptr word found
                have off : ptr < heapLength heap := heapLookup_less heap ptr _ found
                have below : ptr < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le off heapBound
                calc
                  ptr * 2 ^ shiftLength conf < (2 ^ width / 2 ^ shiftLength conf) * 2 ^ shiftLength conf :=
                    Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)
                  _ ≤ 2 ^ width := Nat.div_mul_le_self _ _
              have sameAddress : getAddr (width := width) conf ptr1 (.word 0) = getAddr conf ptr2 (.word 0) := by
                apply WordLocW.word.inj
                simpa only [wordAddr] using addr1.trans addr2.symm
              have samePtr : ptr1 = ptr2 := by
                apply pointerEncoding_injective ptr1 ptr2 (shiftLength conf)
                  (ptrBound ptr1 word1 found1) (ptrBound ptr2 word2 found2) (by simp [shiftLength])
                simpa [getAddr, getLowerBits] using sameAddress
              subst ptr2
              have sameRep : (word64Rep (width := width) (α := WordLocW width) word1) = word64Rep word2 :=
                Option.some.inj (found1.symm.trans found2)
              have sameValue := word64Rep_injective good word1 word2 sameRep
              subst word2
              simpa [doEq] using compare.symm

/-- A bignum heap cell uniquely determines the source integer. This Flapjack
helper uses the original multiword conversion round trip. -/
theorem bignumRep_injective {width : Nat} [NeZero width] (i1 i2 : Int)
    (same : (bignumRep (width := width) (α := WordLocW width) i1) = bignumRep i2) : i1 = i2 := by
  have encoded : (Misc.Multiword.i2mw (width := width) i1) = Misc.Multiword.i2mw i2 := by
    cases h1 : Misc.Multiword.i2mw (width := width) i1 with
    | mk sign1 words1 =>
      cases h2 : Misc.Multiword.i2mw (width := width) i2 with
      | mk sign2 words2 =>
        simp only [bignumRep, h1, h2] at same
        simp only [HeapElement.dataElement.injEq, Prod.mk.injEq, HeapTag.numTag.injEq, true_and] at same
        have recovered := congrArg (List.map (fun v : WordLocW width => match v with
          | .word word => word
          | .loc _ _ => 0)) same.2.2
        have wordsEq : words1 = words2 := by
          simpa only [List.map_map, Function.comp_def, List.map_id'] using recovered
        exact Prod.ext same.2.1 wordsEq
  have decoded := congrArg (Misc.Multiword.mw2i (width := width)) encoded
  simpa only [Misc.Multiword.mw2i_i2mw] using decoded

/-- The number/number case of the pointer-equality theorem. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_pointer_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_pointerEq_numberNumber {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i1 i2 : Int) (location : WordLocW width) (b : Bool) (vars : List (Value × WordLocW width))
    (h : memoryRel conf bigEndian next refs space store memory domain
        ((.number i1, location) :: (.number i2, location) :: vars) ∧
      goodDimindex width ∧ doEq refs (.number i1) (.number i2) = .val b) : b = true := by
  obtain ⟨inv, good, compare⟩ := h
  by_cases small : smallInt width i1 ∨ smallInt width i2
  · obtain ⟨w1, w2, eq1, eq2, same⟩ := memoryRel_numberEq conf bigEndian next refs space store memory domain
      i1 i2 location location vars ⟨inv, small, good⟩
    have sameWord : w1 = w2 := WordLocW.word.inj (eq1.symm.trans eq2)
    have sameValue : i1 = i2 := same.mp sameWord
    subst i2
    simpa [doEq] using compare.symm
  · have large1 : ¬ smallInt width i1 := fun h => small (Or.inl h)
    have large2 : ¬ smallInt width i2 := fun h => small (Or.inr h)
    obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩ := inv
    obtain ⟨roots, absInv, addresses⟩ := wordInv
    obtain ⟨_, _, _, _, stackInv⟩ := absInv
    obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
    cases roots with
    | nil => cases values
    | cons root1 rest =>
      cases rest with
      | nil => cases values with | cons _ tail => cases tail
      | cons root2 rest =>
        cases values with
        | cons first more =>
          cases more with
          | cons second _ =>
            cases addresses with
            | cons addr1 more =>
              cases more with
              | cons addr2 _ =>
                have first := (valueInv_number conf i1 refs root1 f tf heap).mp first
                have second := (valueInv_number conf i2 refs root2 f tf heap).mp second
                simp only [large1, ↓reduceIte] at first
                simp only [large2, ↓reduceIte] at second
                obtain ⟨ptr1, rootEq1, found1⟩ := first
                obtain ⟨ptr2, rootEq2, found2⟩ := second
                subst root1
                subst root2
                have heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf := heapMem.1
                have ptrBound : ∀ ptr value, heapLookup ptr heap = some (bignumRep value) →
                    ptr * 2 ^ shiftLength conf < 2 ^ width := by
                  intro ptr value found
                  have off : ptr < heapLength heap := heapLookup_less heap ptr _ found
                  have below : ptr < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le off heapBound
                  calc
                    ptr * 2 ^ shiftLength conf < (2 ^ width / 2 ^ shiftLength conf) * 2 ^ shiftLength conf :=
                      Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)
                    _ ≤ 2 ^ width := Nat.div_mul_le_self _ _
                have sameAddress : getAddr (width := width) conf ptr1 (.word 0) = getAddr conf ptr2 (.word 0) := by
                  apply WordLocW.word.inj
                  simpa only [wordAddr] using addr1.trans addr2.symm
                have samePtr : ptr1 = ptr2 := by
                  apply pointerEncoding_injective ptr1 ptr2 (shiftLength conf)
                    (ptrBound ptr1 i1 found1) (ptrBound ptr2 i2 found2) (by simp [shiftLength])
                  simpa [getAddr, getLowerBits] using sameAddress
                subst ptr2
                have sameRep : (bignumRep (width := width) (α := WordLocW width) i1) = bignumRep i2 :=
                  Option.some.inj (found1.symm.trans found2)
                have sameValue := bignumRep_injective i1 i2 sameRep
                subst i2
                simpa [doEq] using compare.symm

/-- Equal target locations imply any successful source equality comparison is
true. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_pointer_eq"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_pointerEq {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v1 v2 : Value) (location : WordLocW width) (b : Bool) (vars : List (Value × WordLocW width))
    (h : memoryRel conf bigEndian next refs space store memory domain ((v1, location) :: (v2, location) :: vars) ∧
      goodDimindex width ∧ doEq refs v1 v2 = .val b) : b = true := by
  cases v1 with
  | number i =>
    cases v2 with
    | number j => exact memoryRel_pointerEq_numberNumber conf bigEndian next refs space store memory domain i j location b vars h
    | word64 _ | block _ _ _ | codePtr _ | refPtr _ _ => simp [doEq] at h
  | word64 w =>
    cases v2 with
    | word64 w2 => exact memoryRel_pointerEq_word64Word64 conf bigEndian next refs space store memory domain w w2 location b vars h
    | number _ | block _ _ _ | codePtr _ | refPtr _ _ => simp [doEq] at h
  | block ts tag vals =>
    cases v2 with
    | block ts2 tag2 vals2 =>
      apply memoryRel_pointerEq_blockBlock conf bigEndian next refs space store memory domain
        ts tag ts2 tag2 vals vals2 location b vars ?_ h
      intro child member other loc result tail premises
      exact memoryRel_pointerEq conf bigEndian next refs space store memory domain child other loc result tail premises
    | number _ | word64 _ | codePtr _ | refPtr _ _ => simp [doEq] at h
  | codePtr label => cases v2 <;> simp [doEq] at h
  | refPtr flag ptr =>
    cases v2 with
    | refPtr flag2 ptr2 => exact memoryRel_pointerEq_refRef conf bigEndian next refs space store memory domain flag flag2 ptr ptr2 location b vars h
    | number _ | word64 _ | block _ _ _ | codePtr _ => simp [doEq] at h
termination_by sizeOf v1
decreasing_by
  subst v1
  simp_wf
  have small := List.sizeOf_lt_of_mem (by assumption)
  omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
