import Flapjack.Compiler.Backend.StackRemove.Proofs.StateRelation
import Flapjack.Compiler.Backend.StackRemove.StoreAddress
namespace Flapjack.Compiler.Backend.StackRemove.StoreHeapReads
open Flapjack Flapjack.Compiler.Backend.StackRemove

/-- Flapjack proof infrastructure: extract a concrete slot from the faithful
reverse list heap by induction, preserving modular addresses and arbitrary
payloads. This is not a separately named HOL theorem. -/
theorem wordListRevNth {width : Nat} [NeZero width] {β : Type}
    (base : BitVec width) (values : List β)
    (heap : (BitVec width × β) → Prop) (index : Nat)
    (bound : index < values.length) (assertion : wordListRev base values heap) :
    heap (base - bytesInWord width * BitVec.ofNat width (index + 1), values[index]) := by
  induction values generalizing base heap index with
  | nil => simp at bound
  | cons value values ih =>
    rcases assertion with ⟨head, tail, partition, singleton, rest⟩
    cases index with
    | zero =>
      simp only [List.getElem_cons_zero]
      have member : head (base - bytesInWord width, value) := by
        rw [singleton]
      rw [← partition.1]
      simpa using Or.inl member
    | succ index =>
      have smaller : index < values.length := by simpa using bound
      have member := ih (base - bytesInWord width) tail index smaller rest
      have addressEq : base - bytesInWord width - bytesInWord width * BitVec.ofNat width (index + 1) =
          base - bytesInWord width * BitVec.ofNat width (index + 1 + 1) := by
        simp [BitVec.sub_sub, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_comm]
      rw [addressEq] at member
      rw [← partition.1]
      exact Or.inr member

open Flapjack.Compiler.Backend.StackLang
/-- Flapjack infrastructure identifying the original first-match store slot;
not a standalone HOL declaration. -/
theorem storeSlot (name : StoreName) (membership : name ∈ storeList) :
    ∃ (index : Nat) (bound : index < storeList.length),
      storeList[index] = name ∧ storePos name = index + 1 := by
  cases name with
  | nextFree => exact ⟨0, by decide, rfl, rfl⟩
  | endOfHeap => exact ⟨1, by decide, rfl, rfl⟩
  | heapLength => exact ⟨2, by decide, rfl, rfl⟩
  | otherHeap => exact ⟨3, by decide, rfl, rfl⟩
  | triggerGC => exact ⟨4, by decide, rfl, rfl⟩
  | allocSize => exact ⟨5, by decide, rfl, rfl⟩
  | handler => exact ⟨6, by decide, rfl, rfl⟩
  | globals => exact ⟨7, by decide, rfl, rfl⟩
  | globReal => exact ⟨8, by decide, rfl, rfl⟩
  | progStart => exact ⟨9, by decide, rfl, rfl⟩
  | bitmapBase => exact ⟨10, by decide, rfl, rfl⟩
  | genStart => exact ⟨11, by decide, rfl, rfl⟩
  | codeBuffer => exact ⟨12, by decide, rfl, rfl⟩
  | codeBufferEnd => exact ⟨13, by decide, rfl, rfl⟩
  | bitmapBuffer => exact ⟨14, by decide, rfl, rfl⟩
  | bitmapBufferEnd => exact ⟨15, by decide, rfl, rfl⟩
  | currHeap => simp [storeList] at membership
  | temp value =>
    have values : value = BitVec.ofNat 5 0 ∨ value = BitVec.ofNat 5 1 ∨ value = BitVec.ofNat 5 2 ∨ value = BitVec.ofNat 5 3 ∨ value = BitVec.ofNat 5 4 ∨ value = BitVec.ofNat 5 5 ∨ value = BitVec.ofNat 5 6 ∨ value = BitVec.ofNat 5 7 ∨ value = BitVec.ofNat 5 8 ∨ value = BitVec.ofNat 5 9 ∨ value = BitVec.ofNat 5 10 ∨ value = BitVec.ofNat 5 11 ∨ value = BitVec.ofNat 5 12 ∨ value = BitVec.ofNat 5 13 ∨ value = BitVec.ofNat 5 14 ∨ value = BitVec.ofNat 5 15 ∨ value = BitVec.ofNat 5 16 ∨ value = BitVec.ofNat 5 17 ∨ value = BitVec.ofNat 5 18 ∨ value = BitVec.ofNat 5 19 ∨ value = BitVec.ofNat 5 20 ∨ value = BitVec.ofNat 5 21 ∨ value = BitVec.ofNat 5 22 ∨ value = BitVec.ofNat 5 23 ∨ value = BitVec.ofNat 5 24 ∨ value = BitVec.ofNat 5 25 ∨ value = BitVec.ofNat 5 26 ∨ value = BitVec.ofNat 5 27 ∨ value = BitVec.ofNat 5 28 ∨ value = BitVec.ofNat 5 29 ∨ value = BitVec.ofNat 5 30 ∨ value = BitVec.ofNat 5 31 := by
      simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]
      have bound := value.isLt
      omega
    rcases values with same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same <;> subst value
    · exact ⟨16, by decide, rfl, rfl⟩
    · exact ⟨17, by decide, rfl, rfl⟩
    · exact ⟨18, by decide, rfl, rfl⟩
    · exact ⟨19, by decide, rfl, rfl⟩
    · exact ⟨20, by decide, rfl, rfl⟩
    · exact ⟨21, by decide, rfl, rfl⟩
    · exact ⟨22, by decide, rfl, rfl⟩
    · exact ⟨23, by decide, rfl, rfl⟩
    · exact ⟨24, by decide, rfl, rfl⟩
    · exact ⟨25, by decide, rfl, rfl⟩
    · exact ⟨26, by decide, rfl, rfl⟩
    · exact ⟨27, by decide, rfl, rfl⟩
    · exact ⟨28, by decide, rfl, rfl⟩
    · exact ⟨29, by decide, rfl, rfl⟩
    · exact ⟨30, by decide, rfl, rfl⟩
    · exact ⟨31, by decide, rfl, rfl⟩
    · exact ⟨32, by decide, rfl, rfl⟩
    · exact ⟨33, by decide, rfl, rfl⟩
    · exact ⟨34, by decide, rfl, rfl⟩
    · exact ⟨35, by decide, rfl, rfl⟩
    · exact ⟨36, by decide, rfl, rfl⟩
    · exact ⟨37, by decide, rfl, rfl⟩
    · exact ⟨38, by decide, rfl, rfl⟩
    · exact ⟨39, by decide, rfl, rfl⟩
    · exact ⟨40, by decide, rfl, rfl⟩
    · exact ⟨41, by decide, rfl, rfl⟩
    · exact ⟨42, by decide, rfl, rfl⟩
    · exact ⟨43, by decide, rfl, rfl⟩
    · exact ⟨44, by decide, rfl, rfl⟩
    · exact ⟨45, by decide, rfl, rfl⟩
    · exact ⟨46, by decide, rfl, rfl⟩
    · exact ⟨47, by decide, rfl, rfl⟩

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original store-heap read: ordered store membership, source lookup,
and all five native heap assertions derive the actual target load, with no
successful-target or derived-domain assumption. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_load_lemma"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem memLoadLemma {width : Nat} [NeZero width] {C F : Type}
    (name : StoreName) (source target : StackSemStateFiniteExact width C F)
    (value : WordLocW width) (base : BitVec width)
    (hypothesis : name ∈ storeList ∧
      source.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) = some value ∧
      SetSep.star
        (SetSep.star
          (SetSep.star
            (SetSep.star (memoryHOL source.memory (fun address => source.mdomain address = true))
              (Misc.wordList
                (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width)
                ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word)))
            (Misc.wordListExists
              ((theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width) +
                bytesInWord width * BitVec.ofNat width (source.dataBuffer.buffer.length + source.bitmaps.length))
              source.dataBuffer.spaceLeft))
          (wordStoreHOL base source.store))
        (Misc.wordList base source.stack)
        (SetSep.fun2Set (target.memory, fun address => target.mdomain address = true))) :
    StackSemStateOps.memLoad (base + storeOffset name) target = some value := by
  rcases hypothesis with ⟨membership, lookup, heaps⟩
  rcases heaps with ⟨heap4, heapStack, split4, assertion4, _stack⟩
  rcases assertion4 with ⟨heap3, heapStore, split3, _assertion3, storeAssertion⟩
  obtain ⟨index, bound, nameEq, positionEq⟩ := storeSlot name membership
  let values := storeList.map fun slot =>
    (source.store.lookup (StackSemRegisterTransfers.storeOfSyntax slot)).getD (.word 0)
  have mappedBound : index < values.length := by simpa [values] using bound
  have member := wordListRevNth base values heapStore index mappedBound storeAssertion
  have entryEq : values[index] = value := by
    simp only [values, List.getElem_map, nameEq, lookup, Option.getD_some]
  have addressEq : base - bytesInWord width * BitVec.ofNat width (index + 1) =
      base + storeOffset name := by
    simp [storeOffset, wordOffset, positionEq, bytesInWord, BitVec.ofNat_mul,
      BitVec.sub_eq_add_neg]
  rw [addressEq, entryEq] at member
  have inHeap4 : heap4 (base + storeOffset name, value) := by
    rw [← split3.1]
    exact Or.inr member
  have inTarget : SetSep.fun2Set (target.memory, fun address => target.mdomain address = true)
      (base + storeOffset name, value) := by
    rw [← split4.1]
    exact Or.inl inHeap4
  have loadFacts := (SetSep.fun2SetThm target.memory (fun address => target.mdomain address = true)
    (base + storeOffset name) value).mp inTarget
  simp only [StackSemStateOps.memLoad, loadFacts.1, loadFacts.2, ite_true]

/-- Full original store-slot domain theorem: the complete five-factor heap
and ordered store membership suffice without any source store lookup premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "mem_load_lemma2"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem memLoadLemma2 {width : Nat} [NeZero width] {SourceC SourceF TargetC TargetF : Type}
    (name : StoreName) (source : StackSemStateFiniteExact width SourceC SourceF)
    (target : StackSemStateFiniteExact width TargetC TargetF)
    (base : BitVec width)
    (hypothesis : name ∈ storeList ∧
      SetSep.star
        (SetSep.star
          (SetSep.star
            (SetSep.star (memoryHOL source.memory (fun address => source.mdomain address = true))
              (Misc.wordList
                (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width)
                ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word)))
            (Misc.wordListExists
              ((theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width) +
                bytesInWord width * BitVec.ofNat width (source.dataBuffer.buffer.length + source.bitmaps.length))
              source.dataBuffer.spaceLeft))
          (wordStoreHOL base source.store))
        (Misc.wordList base source.stack)
        (SetSep.fun2Set (target.memory, fun address => target.mdomain address = true))) :
    target.mdomain (base + storeOffset name) = true := by
  rcases hypothesis with ⟨membership, heaps⟩
  rcases heaps with ⟨heap4, heapStack, split4, assertion4, _stack⟩
  rcases assertion4 with ⟨heap3, heapStore, split3, _assertion3, storeAssertion⟩
  obtain ⟨index, bound, nameEq, positionEq⟩ := storeSlot name membership
  let values := storeList.map fun slot =>
    (source.store.lookup (StackSemRegisterTransfers.storeOfSyntax slot)).getD (.word 0)
  have mappedBound : index < values.length := by simpa [values] using bound
  have member := wordListRevNth base values heapStore index mappedBound storeAssertion
  have addressEq : base - bytesInWord width * BitVec.ofNat width (index + 1) =
      base + storeOffset name := by
    simp [storeOffset, wordOffset, positionEq, bytesInWord, BitVec.ofNat_mul,
      BitVec.sub_eq_add_neg]
  rw [addressEq] at member
  have inHeap4 : heap4 (base + storeOffset name, values[index]) := by
    rw [← split3.1]
    exact Or.inr member
  have inTarget : SetSep.fun2Set (target.memory, fun address => target.mdomain address = true)
      (base + storeOffset name, values[index]) := by
    rw [← split4.1]
    exact Or.inl inHeap4
  have loadFacts := (SetSep.fun2SetThm target.memory (fun address => target.mdomain address = true)
    (base + storeOffset name) values[index]).mp inTarget
  exact loadFacts.2

end Flapjack.Compiler.Backend.StackRemove.StoreHeapReads
