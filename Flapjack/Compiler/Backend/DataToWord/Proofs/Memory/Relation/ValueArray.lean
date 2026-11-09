module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArray
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockElement

@[expose] public section

/-! Concrete value-array headers from the memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend
open Classical
noncomputable section

/-- Read a reference-array header from a word heap (Flapjack helper). -/
private theorem refHeader {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (heap : ValueHeap width) (index : Nat) (roots : List (HeapAddress (WordLocW width)))
    (curr : BitVec width) (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (refBlock roots))
    (assertion : wordHeap curr heap conf whole) :
    whole (curr + StackRemove.bytesInWord width * BitVec.ofNat width index,
      .word (DataToWord.makeHeader conf 2 roots.length)) ∧
    roots.length < 2 ^ (width - 4) ∧
    WordGcFunctions.decodeLength conf (DataToWord.makeHeader conf 2 roots.length) = BitVec.ofNat width roots.length := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index (refBlock roots) found
  subst heap
  subst index
  rw [wordHeapAppend] at assertion
  obtain ⟨beforeHeap, restHeap, split1, _, restAssertion⟩ := assertion
  change SetSep.star (wordEl _ (refBlock roots) conf) (wordHeap _ after conf) restHeap at restAssertion
  obtain ⟨elementHeap, suffixHeap, split2, elementAssertion, _⟩ := restAssertion
  simp only [wordEl, refBlock, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map] at elementAssertion
  obtain ⟨listHeap, pureHeap, split3, listAssertion, pureAssertion⟩ := elementAssertion
  obtain ⟨singleton, tailHeap, split4, singletonAssertion, _⟩ := listAssertion
  have member1 : singleton (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before),
      .word (DataToWord.makeHeader conf 2 roots.length)) := by rw [singletonAssertion]
  have member2 : listHeap _ := (iff_of_eq (congrFun split4.1 _)).mp (Or.inl member1)
  have member3 : elementHeap _ := (iff_of_eq (congrFun split3.1 _)).mp (Or.inl member2)
  have member4 : restHeap _ := (iff_of_eq (congrFun split2.1 _)).mp (Or.inl member3)
  have member5 : whole _ := (iff_of_eq (congrFun split1.1 _)).mp (Or.inr member4)
  exact ⟨member5, pureAssertion.2.1, pureAssertion.2.2.1⟩

/-- Reference-array header tag bits at supported widths (Flapjack helper). -/
private theorem refHeaderBits {width : Nat} [NeZero width] (conf : DataToWord.Config) (len : Nat)
    (good : goodDimindex width) (bound : conf.lenSize + 7 < width) :
    (DataToWord.makeHeader (width := width) conf 2 len).getLsbD 3 = true ∧
    (DataToWord.makeHeader (width := width) conf 2 len).getLsbD 2 = false ∧
    (DataToWord.makeHeader (width := width) conf 2 len).getLsbD 4 = false := by
  have h2 : ¬ (2 : Nat) ≥ width - conf.lenSize := by omega
  have h4 : ¬ (4 : Nat) ≥ width - conf.lenSize := by omega
  rcases good with hw | hw <;> subst width <;> simp [DataToWord.makeHeader, h2, h4]

/-- A related value-array reference has the original concrete header and length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_ValueArray_IMP"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_valueArrayImp {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bit : Bool) (index : Nat) (values : List DataSem.Value) (location : WordLocW width)
    (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.refPtr bit index, location) :: vars) ∧
      sptLookup index refs = some (.valueArray values) ∧ goodDimindex width →
    ∃ w address header : BitVec width, location = .word w ∧ w.getLsbD 0 = true ∧
      header.getLsbD 3 = true ∧ header.getLsbD 2 = false ∧ header.getLsbD 4 = false ∧
      getRealSimpleAddr conf store w = some address ∧ getRealAddr conf store w = some address ∧
      memory address = .word header ∧ domain address = true ∧
      WordGcFunctions.decodeLength conf header = BitVec.ofNat width values.length ∧
      values.length < 2 ^ (width - 4) := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩, found, good⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, pairs, referenceInv⟩ := stackInv
  cases roots with
  | nil => cases pairs
  | cons root rest =>
    cases pairs with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        have noThunk : ∀ mode value, sptLookup index refs ≠ some (.thunk mode value) := by
          intro mode value eq
          rw [found] at eq
          cases eq
        obtain ⟨domainF, _, rootEq⟩ :=
          (valueInv_refPtr_notThunk conf bit index refs root f tf heap noThunk).mp related
        obtain ⟨ptr, ffound⟩ := domainF
        rw [found, holFapply_of_lookup ffound] at rootEq
        have rootEq' : root = .pointer ptr (.word 0) := by simpa [refPtrAnnot] using rootEq
        rw [rootEq'] at projected
        have locationEq : location = .word (getAddr conf ptr (.word 0)) := by
          simpa [wordAddr] using projected.symm
        have reachable : reachableRefs ((DataSem.Value.refPtr bit index) :: vars.map Prod.fst) refs index := by
          exact ⟨.refPtr bit index, index, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
        have cellInv := referenceInv index ⟨reachable, ⟨ptr, ffound⟩⟩
        obtain ⟨children, cell, pair⟩ : ∃ children, heapLookup ptr heap = some (refBlock children) ∧
            List.Forall₂ (fun address value => valueInv conf value refs (address, f, tf, heap)) children values := by
          simpa [bcRefInv, ffound, found] using cellInv
        have childLen : children.length = values.length := pair.length_eq
        obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
        obtain ⟨active, inactive, split, activeHeap, _⟩ := heapAssertion
        obtain ⟨member, lenBound, decoded⟩ := refHeader conf heap ptr children curr active cell activeHeap
        have graph : SetSep.fun2Set (memory, fun addr => domain addr = true)
            (curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
              .word (DataToWord.makeHeader conf 2 children.length)) := by
          rw [← split.1]
          exact Or.inl member
        obtain ⟨memEq, inDomain⟩ := (SetSep.fun2SetThm memory _ _ _).mp graph
        have real := getRealAddr_getAddr conf store heap ptr _ curr (.word 0) ⟨heapMem.1, cell, stored, good⟩
        have bits := refHeaderBits conf children.length good heapMem.2.2.2.2.1
        refine ⟨getAddr conf ptr (.word 0), curr + StackRemove.bytesInWord width * BitVec.ofNat width ptr,
          DataToWord.makeHeader conf 2 children.length, locationEq, getAddr_lowBit conf ptr _,
          bits.1, bits.2.1, bits.2.2, ?_, ?_, memEq, inDomain, ?_, ?_⟩
        · simpa [BitVec.mul_comm] using real.1
        · simpa [BitVec.mul_comm] using real.2
        · simpa [childLen] using decoded
        · simpa [childLen] using lenBound

/-- Byte-array header tag bits at supported widths (Flapjack helper). -/
private theorem byteHeaderBits {width : Nat} [NeZero width] (conf : DataToWord.Config) (len : Nat) (flag : Bool)
    (good : goodDimindex width) (bound : conf.lenSize + 7 < width) :
    (DataToWord.makeByteHeader (width := width) conf flag len).getLsbD 3 = false ∧
    (DataToWord.makeByteHeader (width := width) conf flag len).getLsbD 2 = true := by
  rcases good with hw | hw <;> subst width
  · have h3 : ¬ (3 : Nat) ≥ 32 - 2 - conf.lenSize := by omega
    cases flag <;> simp [DataToWord.makeByteHeader, h3]
  · have h3 : ¬ (3 : Nat) ≥ 64 - 3 - conf.lenSize := by omega
    cases flag <;> simp [DataToWord.makeByteHeader, h3]

/-- A comparison reference points to a header with the original tag-bit relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_RefPtr_T_IMP"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_refPtrTrueImp {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (index : Nat) (location : WordLocW width) (vars : List (DataSem.Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((.refPtr true index, location) :: vars) ∧
      goodDimindex width →
    ∃ w address header : BitVec width, location = .word w ∧ w.getLsbD 0 = true ∧
      (header.getLsbD 3 = true ↔ header.getLsbD 2 = false) ∧
      getRealAddr conf store w = some address ∧ getRealSimpleAddr conf store w = some address ∧
      memory address = .word header ∧ domain address = true := by
  rintro ⟨rel, good⟩
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
  obtain ⟨cell, found⟩ := memoryRel_refPtrExists conf be next refs space store memory domain true index location vars rel
  cases cell with
  | valueArray values =>
    obtain ⟨w, address, header, loc, low, bit3, bit2, _, simple, real, mem, indom, _, _⟩ :=
      memoryRel_valueArrayImp conf be next refs space store memory domain true index values location vars ⟨rel, found, good⟩
    exact ⟨w, address, header, loc, low, by simp [bit3, bit2], real, simple, mem, indom⟩
  | byteArray flag bytes =>
    obtain ⟨w, address, loc, low, real, simple, mem, indom, bound, _⟩ :=
      memoryRel_byteArrayHeader conf be next refs space store memory domain true flag index bytes location vars rel found good
    obtain ⟨bit3, bit2⟩ := byteHeaderBits conf bytes.length flag good bound
    exact ⟨w, address, DataToWord.makeByteHeader conf flag bytes.length,
      loc, low, by simp [bit3, bit2], real, simple, mem, indom⟩
  | thunk mode value => exact False.elim (noThunk mode value found)
  | mutBlock tag finalised left child right =>
    exact False.elim (memoryRel_refPtrTrueNotMutBlock conf be next refs space store memory domain index location vars
      tag finalised left child right ⟨rel, found⟩)

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
