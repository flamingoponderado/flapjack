import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueArray
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockElement

/-! Concrete representation of source Word64 values. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend
open Classical
noncomputable section

/-- Read the header and payload words of an abstract Word64 cell (Flapjack helper). -/
private theorem word64Heap {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (heap : ValueHeap width) (index : Nat) (value : BitVec 64) (curr : BitVec width)
    (whole : (BitVec width × WordLocW width) → Prop)
    (good : goodDimindex width) (found : heapLookup index heap = some (word64Rep value))
    (h : wordHeap curr heap conf whole) :
    let count := if width < 64 then 2 else 1
    let first := if width < 64 then (value >>> 32).setWidth width else value.setWidth width
    let address := curr + StackRemove.bytesInWord width * BitVec.ofNat width index
    whole (address, .word (DataToWord.makeHeader conf 3 count)) ∧
    whole (address + StackRemove.bytesInWord width, .word first) ∧
    (width < 64 → whole (address + (StackRemove.bytesInWord width <<< 1), .word (value.setWidth width))) ∧
    WordGcFunctions.decodeLength conf (DataToWord.makeHeader conf 3 count) = BitVec.ofNat width count := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index (word64Rep value) found
  subst heap
  subst index
  rw [wordHeapAppend] at h
  obtain ⟨beforeHeap, restHeap, split1, _, restAssertion⟩ := h
  change SetSep.star (wordEl _ (word64Rep value) conf) (wordHeap _ after conf) restHeap at restAssertion
  obtain ⟨elementHeap, suffixHeap, split2, elementAssertion, _⟩ := restAssertion
  by_cases small : width < 64
  · simp only [word64Rep, small, ↓reduceIte, wordEl, wordPayload, List.isEmpty_nil,
      Bool.true_and, List.length_cons, List.length_nil, Nat.reduceAdd] at elementAssertion
    obtain ⟨listHeap, pureHeap, split3, listAssertion, pureAssertion⟩ := elementAssertion
    have lift : ∀ e, listHeap e → whole e := by
      intro e member
      have he : elementHeap e := (iff_of_eq (congrFun split3.1 e)).mp (Or.inl member)
      have hr : restHeap e := (iff_of_eq (congrFun split2.1 e)).mp (Or.inl he)
      exact (iff_of_eq (congrFun split1.1 e)).mp (Or.inr hr)
    have h0 := lift _ (wordList_indexMember
      [.word (DataToWord.makeHeader conf 3 2), .word ((value >>> 32).setWidth width), .word (value.setWidth width)]
      0 (by simp) _ listHeap listAssertion)
    have h1 := lift _ (wordList_indexMember
      [.word (DataToWord.makeHeader conf 3 2), .word ((value >>> 32).setWidth width), .word (value.setWidth width)]
      1 (by simp) _ listHeap listAssertion)
    have h2 := lift _ (wordList_indexMember
      [.word (DataToWord.makeHeader conf 3 2), .word ((value >>> 32).setWidth width), .word (value.setWidth width)]
      2 (by simp) _ listHeap listAssertion)
    simp only [small, ↓reduceIte, true_implies]
    refine ⟨?_, ?_, ?_, pureAssertion.2.2.1⟩
    · simpa using h0
    · simpa using h1
    · have shiftEq : (StackRemove.bytesInWord width <<< 1) =
          StackRemove.bytesInWord width + StackRemove.bytesInWord width := by
        rcases good with hw | hw <;> subst width <;> decide
      rw [shiftEq]
      simpa [BitVec.two_mul, BitVec.add_assoc] using h2
  · simp only [word64Rep, small, ↓reduceIte, wordEl, wordPayload, List.isEmpty_nil,
      Bool.true_and, List.length_cons, List.length_nil, Nat.reduceAdd] at elementAssertion
    obtain ⟨listHeap, pureHeap, split3, listAssertion, pureAssertion⟩ := elementAssertion
    have lift : ∀ e, listHeap e → whole e := by
      intro e member
      have he : elementHeap e := (iff_of_eq (congrFun split3.1 e)).mp (Or.inl member)
      have hr : restHeap e := (iff_of_eq (congrFun split2.1 e)).mp (Or.inl he)
      exact (iff_of_eq (congrFun split1.1 e)).mp (Or.inr hr)
    have h0 := lift _ (wordList_indexMember
      [.word (DataToWord.makeHeader conf 3 1), .word (value.setWidth width)] 0 (by simp) _ listHeap listAssertion)
    have h1 := lift _ (wordList_indexMember
      [.word (DataToWord.makeHeader conf 3 1), .word (value.setWidth width)] 1 (by simp) _ listHeap listAssertion)
    simp only [small, ↓reduceIte]
    exact ⟨by simpa using h0, by simpa using h1, fun h => False.elim h, pureAssertion.2.2.1⟩

/-- Word64 header tag bits at supported widths (Flapjack helper). -/
private theorem word64HeaderBits {width : Nat} [NeZero width] (conf : DataToWord.Config) (len : Nat)
    (good : goodDimindex width) (bound : conf.lenSize + 7 < width) :
    (DataToWord.makeHeader (width := width) conf 3 len).getLsbD 3 = true ∧
    (DataToWord.makeHeader (width := width) conf 3 len).getLsbD 4 = false ∧
    (DataToWord.makeHeader (width := width) conf 3 len).getLsbD 2 = true := by
  have h4 : ¬ (4 : Nat) ≥ width - conf.lenSize := by omega
  rcases good with hw | hw <;> subst width <;> simp [DataToWord.makeHeader, h4]

/-- A related Word64 value exposes its complete concrete memory layout. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Word64_IMP"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_word64Imp {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (value : BitVec 64) (location : WordLocW width) (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.word64 value, location) :: vars) ∧
      goodDimindex width →
    ∃ (ptr : Nat) (address header : BitVec width),
      location = .word (getAddr conf ptr (.word 0)) ∧
      getRealAddr conf store (getAddr conf ptr (.word 0)) = some address ∧
      domain address = true ∧ memory address = .word header ∧
      header.getLsbD 3 = true ∧ header.getLsbD 4 = false ∧ header.getLsbD 2 = true ∧
      domain (address + StackRemove.bytesInWord width) = true ∧
      if width < 64 then
        memory (address + StackRemove.bytesInWord width) = .word ((value >>> 32).setWidth width) ∧
        domain (address + (StackRemove.bytesInWord width <<< 1)) = true ∧
        memory (address + (StackRemove.bytesInWord width <<< 1)) = .word (value.setWidth width) ∧
        WordGcFunctions.decodeLength conf header = 2 ∧ header = DataToWord.makeHeader conf 3 2
      else
        memory (address + StackRemove.bytesInWord width) = .word (value.setWidth width) ∧
        WordGcFunctions.decodeLength conf header = 1 ∧ header = DataToWord.makeHeader conf 3 1 := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩, good⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root rest =>
    cases values with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        obtain ⟨ptr, rootEq, cell⟩ := (valueInv_word64 conf value refs root f tf heap).mp related
        rw [rootEq] at projected
        have locEq : location = .word (getAddr conf ptr (.word 0)) := by simpa [wordAddr] using projected.symm
        obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
        obtain ⟨active, inactive, split, activeHeap, _⟩ := heapAssertion
        obtain ⟨headerMember, firstMember, secondMember, decoded⟩ :=
          word64Heap conf heap ptr value curr active good cell activeHeap
        have graph : ∀ e, active e → SetSep.fun2Set (memory, fun addr => domain addr = true) e := by
          intro e member
          rw [← split.1]
          exact Or.inl member
        have headerFacts := (SetSep.fun2SetThm memory _ _ _).mp (graph _ headerMember)
        have firstFacts := (SetSep.fun2SetThm memory _ _ _).mp (graph _ firstMember)
        have addrCalc := (getRealAddr_getAddr conf store heap ptr _ curr (.word 0)
          ⟨heapMem.1, cell, stored, good⟩).2
        have bits := word64HeaderBits conf (if width < 64 then 2 else 1) good heapMem.2.2.2.2.1
        refine ⟨ptr, curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
          DataToWord.makeHeader conf 3 (if width < 64 then 2 else 1), locEq, ?_,
          headerFacts.2, headerFacts.1, bits.1, bits.2.1, bits.2.2, firstFacts.2, ?_⟩
        · simpa [BitVec.mul_comm] using addrCalc
        · by_cases small : width < 64
          · have secondFacts := (SetSep.fun2SetThm memory _ _ _).mp (graph _ (secondMember small))
            simp only [small, ↓reduceIte] at firstFacts decoded ⊢
            exact ⟨firstFacts.1, secondFacts.2, secondFacts.1, decoded, True.intro⟩
          · simp only [small, ↓reduceIte] at firstFacts decoded ⊢
            exact ⟨firstFacts.1, decoded, True.intro⟩

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
