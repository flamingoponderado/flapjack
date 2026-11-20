module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.Semantics.WordSem.Inst
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordMemoryEquality
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64

@[expose] public section

/-! Constant Word64 comparisons in the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend
open Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Recover header encodability from a separated Word64 heap cell. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem word64HeapHeader {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (heap : ValueHeap width) (index : Nat) (value : BitVec 64) (curr : BitVec width)
    (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (word64Rep value))
    (h : wordHeap curr heap conf whole) :
    (DataToWord.encodeHeader (width := width) conf 3 (if width < 64 then 2 else 1)).isSome = true := by
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
    simpa [small] using pureAssertion.2.2.2
  · simp only [word64Rep, small, ↓reduceIte, wordEl, wordPayload, List.isEmpty_nil,
      Bool.true_and, List.length_cons, List.length_nil, Nat.reduceAdd] at elementAssertion
    obtain ⟨listHeap, pureHeap, split3, listAssertion, pureAssertion⟩ := elementAssertion
    simpa [small] using pureAssertion.2.2.2

/-- Derive Word64 header encodability from the memory relation. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem word64HeaderExists {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (value : BitVec 64) (location : WordLocW width) (vars : List (DataSem.Value × WordLocW width))
    (rel : memoryRel conf be next refs space store memory domain ((.word64 value, location) :: vars)) :
    (DataToWord.encodeHeader (width := width) conf 3 (if width < 64 then 2 else 1)).isSome = true := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩ := rel
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root rest =>
    cases values with
    | cons related _ =>
      obtain ⟨ptr, rootEq, cell⟩ := (valueInv_word64 conf value refs root f tf heap).mp related
      obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
      obtain ⟨active, inactive, split, activeHeap, _⟩ := heapAssertion
      exact word64HeapHeader conf heap ptr value curr active cell activeHeap

/-- Relate HOL high-word extraction to the 32-bit payload. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem extractHigh32 (v : BitVec 64) : holWordExtract 63 32 v 32 = (v >>> 32).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [holWordExtract, BitVec.toNat_ushiftRight]

/-- Relate HOL low-word extraction to the 32-bit payload. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem extractLow32 (v : BitVec 64) : holWordExtract 31 0 v 32 = v.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [holWordExtract]

/-- Relate HOL full-word extraction to the 64-bit payload. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem extractAll64 (v : BitVec 64) : holWordExtract 63 0 v 64 = v.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [holWordExtract, Nat.mod_eq_of_lt v.isLt]

/-- A related Word64 compares against the exact constant payload and header. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Word64_const_test"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_word64ConstTest {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i j : BitVec 64) (location : WordLocW width) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (h : memoryRel conf be next refs space store memory domain ((.word64 i, location) :: vars) ∧
      goodDimindex width) :
    ∃ (w a : BitVec width) (words : List (BitVec width)) (header : BitVec width),
      location = .word w ∧ getRealAddr conf store w = some a ∧
      wordMemEq (a + StackRemove.bytesInWord width) words domain memory = some (decide (i = j)) ∧
      DataToWord.encodeHeader conf 3 words.length = some header ∧
      if width < 64 then words = [holWordExtract 63 32 j width, holWordExtract 31 0 j width]
      else words = [holWordExtract 63 0 j width] := by
  obtain ⟨ptr, address, header, loc, addr, domainHead, memHead, bit3, bit4, bit2, domain1, more⟩ :=
    memoryRel_word64Imp conf be next refs space store memory domain i location vars h
  have encodedExists := word64HeaderExists conf be next refs space store memory domain i location vars h.1
  rcases h.2 with dim32 | dim64
  · subst width
    obtain ⟨mem1, domain2, mem2, _, _⟩ := more
    cases encoded : DataToWord.encodeHeader (width := 32) conf 3 2 with
    | none => simp [encoded] at encodedExists
    | some hd =>
      refine ⟨getAddr conf ptr (.word 0), address, [(j >>> 32).setWidth 32, j.setWidth 32], hd,
        loc, addr, ?_, ?_, by simp [extractHigh32, extractLow32]⟩
      · have domainSecond : domain ((address + StackRemove.bytesInWord 32) + StackRemove.bytesInWord 32) = true := by
          simpa [StackRemove.bytesInWord, BitVec.add_assoc] using domain2
        have memSecond : memory ((address + StackRemove.bytesInWord 32) + StackRemove.bytesInWord 32) = .word (i.setWidth 32) := by
          simpa [StackRemove.bytesInWord, BitVec.add_assoc] using mem2
        simp only [wordMemEq, domain1, ↓reduceIte, mem1, domainSecond, memSecond]
        by_cases equal : i = j
        · subst j
          simp
        · by_cases hi : (i >>> 32).setWidth 32 = (j >>> 32).setWidth 32
          · have lo : i.setWidth 32 ≠ j.setWidth 32 := by
              intro same
              exact equal ((bitWord64Split i j).mp ⟨hi, same⟩)
            simp [lo, equal]
          · simp [equal]
            intro same
            exact (hi same).elim
      · simpa using encoded
  · subst width
    simp only [show ¬ (64 : Nat) < 64 by decide, if_false] at more encodedExists
    obtain ⟨mem1, _, _⟩ := more
    cases encoded : DataToWord.encodeHeader (width := 64) conf 3 1 with
    | none => simp [encoded] at encodedExists
    | some hd =>
      refine ⟨getAddr conf ptr (.word 0), address, [j.setWidth 64], hd,
        loc, addr, ?_, ?_, by simp [extractAll64]⟩
      · by_cases equal : i = j <;> simp [wordMemEq, domain1, mem1, equal]
      · simpa using encoded
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
