module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockElement
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute

@[expose] public section

/-! Stack-invariant facts for exposing a block's child. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Adding an already reachable value to the stack does not change the set of
all timestamps. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_head_eq"]
theorem allTimestamps_headEq {α : Type} (value : Value) (refs : Spt (BvlSem.Ref Value))
    (stack : List Value) (_ts : α) (member : allValues refs stack value) :
    allTimestamps refs stack = allTimestamps refs (value :: stack) := by
  funext stamp
  apply propext
  constructor
  · rintro ⟨v, inRef | inStack, timestamp⟩
    · exact ⟨v, Or.inl inRef, timestamp⟩
    · exact ⟨v, Or.inr (List.mem_cons_of_mem value inStack), timestamp⟩
  · rintro ⟨v, inRef | inStack, timestamp⟩
    · exact ⟨v, Or.inl inRef, timestamp⟩
    · rcases List.mem_cons.mp inStack with equal | old
      · subst v
        exact mem_allTimestamps value stamp stack refs ⟨member, timestamp⟩
      · exact ⟨v, Or.inr old, timestamp⟩

/-- Values reachable after pushing a child of a block were already reachable
from the stack containing its parent. This is Flapjack invariant infrastructure. -/
theorem allValues_blockChildSubset (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (stamp tag : Nat) (children : List Value) (child value : Value) (member : child ∈ children) :
    allValues refs (child :: .block stamp tag children :: stack) value →
    allValues refs (.block stamp tag children :: stack) value := by
  intro found
  rcases found with inArray | inThunk | inMut | inStack
  · exact Or.inl inArray
  · exact Or.inr (Or.inl inThunk)
  · exact Or.inr (Or.inr (Or.inl inMut))
  · apply Or.inr (Or.inr (Or.inr ?_))
    have split : valueListValues (child :: .block stamp tag children :: stack) =
        valueListValues [child] ++ valueListValues (.block stamp tag children :: stack) := by
      simpa using valueListValues_append [child] (.block stamp tag children :: stack)
    rw [split, List.mem_append] at inStack
    rcases inStack with inChild | inOld
    · have nested := valueListValues_singleton_subset children child value member inChild
      simp only [valueListValues, List.mem_cons, List.mem_append]
      exact Or.inl (Or.inr nested)
    · exact inOld

/-- Adding a selected block child preserves timestamp uniqueness for all blocks. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_el"]
theorem blocksUnique_el (i : Nat) (children stack : List Value) (next : Nat)
    (refs : Spt (BvlSem.Ref Value)) (stamp tag : Nat)
    (bound : i < children.length)
    (unique : blocksUnique next (allValues refs (.block stamp tag children :: stack))) :
    blocksUnique next (allValues refs (children[i] :: .block stamp tag children :: stack)) := by
  intro ts tag1 xs1 tag2 xs2 ⟨first, nonempty1, second, nonempty2⟩
  have childMember : children[i] ∈ children := List.getElem_mem bound
  exact unique ts tag1 xs1 tag2 xs2
    ⟨allValues_blockChildSubset refs stack stamp tag children children[i] _ childMember first,
      nonempty1, allValues_blockChildSubset refs stack stamp tag children children[i] _ childMember second,
      nonempty2⟩

/-- Exposing an in-bounds block child preserves the complete abstract heap
invariant. The returned child root is selected from the parent's heap cell.
This Flapjack theorem isolates the invariant part of `el_thm`. -/
theorem absMlInv_blockChild {width : Nat} [NeZero width] (conf : Config)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit next : Nat)
    (stamp tag : Nat) (children : List Value) (i : Nat) (bound : i < children.length)
    (inv : absMlInv conf (.block stamp tag children :: stack) refs
      (roots, heap, bigEndian, a, sp, sp1, gens) limit next) :
    ∃ (parentRoot childRoot : HeapAddress (WordLocW width)) (rest : List (HeapAddress (WordLocW width)))
      (ptr : Nat) (annotation : WordLocW width) (childRoots : List (HeapAddress (WordLocW width)))
      (childBound : i < childRoots.length),
      roots = parentRoot :: rest ∧ parentRoot = .pointer ptr annotation ∧
      heapLookup ptr heap = some (blockRep tag childRoots) ∧ childRoot = childRoots[i] ∧
      absMlInv conf (children[i] :: .block stamp tag children :: stack) refs
        (childRoot :: roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  obtain ⟨rootOk, heapOk', gc, unused, stackInv⟩ := inv
  obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimestamps, tfBound, endian, unique, related, cells⟩ := stackInv
  cases roots with
  | nil => cases related
  | cons parentRoot rest =>
    cases related with
    | cons parentRelated remaining =>
      have nonempty : children ≠ [] := by
        intro empty
        subst children
        simp at bound
      obtain ⟨ptr, childRoots, pair, lookup, rootEq, cell⟩ :=
        (valueInv_nonemptyBlock conf stamp tag children refs parentRoot f tf heap nonempty).mp parentRelated
      subst parentRoot
      have childBound : i < childRoots.length := by rw [← pair.length_eq]; exact bound
      have childRelated := pair.get bound childBound
      have childMember : children[i] ∈ children := List.getElem_mem bound
      have parentValues : allValues refs (.block stamp tag children :: stack) children[i] := by
        apply allValues_blockChildSubset refs stack stamp tag children children[i] _ childMember
        exact mem_stack_allValues _ _ refs (by simp)
      refine ⟨.pointer ptr (.word (ptrBits conf tag childRoots.length)), childRoots[i], rest, ptr,
        .word (ptrBits conf tag childRoots.length), childRoots, childBound, rfl, rfl, cell, rfl, ?_⟩
      refine ⟨?_, heapOk', gc, unused, ?_⟩
      · intro target annotation member
        rcases List.mem_cons.mp member with eq | old
        · have inChildren : HeapAddress.pointer target annotation ∈ childRoots := by
            rw [eq]
            exact List.getElem_mem childBound
          apply heapOk'.2.2 childRoots childRoots.length (.blockTag tag, []) target annotation
          refine ⟨?_, inChildren⟩
          simpa only [blockRep] using heapLookup_mem heap ptr (blockRep tag childRoots) cell
        · exact rootOk target annotation old
      · refine ⟨f, tf, fInj, fDomain, tfInj, ?_, tfBound, endian, ?_, ?_, ?_⟩
        · intro ts dom
          rw [← allTimestamps_headEq children[i] refs (.block stamp tag children :: stack) () parentValues]
          exact tfTimestamps ts dom
        · exact blocksUnique_el i children stack next refs stamp tag bound unique
        · exact .cons childRelated (.cons parentRelated remaining)
        · intro n ⟨reachable, dom⟩
          apply cells n
          refine ⟨?_, dom⟩
          obtain ⟨source, start, inStack, inRefs, path⟩ := reachable
          rcases List.mem_cons.mp inStack with eq | old
          · subst source
            refine ⟨.block stamp tag children, start, by simp, ?_, path⟩
            simp only [getRefs, List.mem_flatMap]
            exact ⟨children[i], childMember, inRefs⟩
          · exact ⟨source, start, old, inRefs, path⟩

/-- Reading a child from a related block extends the full memory relation
with the selected source value and its concrete word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_El_any"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_elAny {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List Value) (location : WordLocW width)
    (vars : List (Value × WordLocW width)) (i : Nat) (bound : i < values.length)
    (h : memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, location) :: vars) ∧
      goodDimindex width) :
    ∃ w addr _unused : BitVec width,
      location = .word w ∧ getRealAddr conf store w = some addr ∧
      domain (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i) = true ∧
      memoryRel conf bigEndian next refs space store memory domain
        ((values[i], memory (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i)) ::
          (.block stamp tag values, location) :: vars) := by
  obtain ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩, good⟩ := h
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  obtain ⟨parent, child, rest, ptr, annot, childRoots, childBound, rootsEq, parentEq, cell, childEq, extended⟩ :=
    absMlInv_blockChild conf (vars.map Prod.fst) refs roots heap bigEndian a sp sp1 gens limit next
      stamp tag values i bound absInv
  subst roots
  cases addresses with
  | cons parentAddr restAddresses =>
    subst parent
    obtain ⟨addr, addressEq, memoryEq, domainEq⟩ :=
      heapInMemoryStore_blockElement conf heap ptr tag childRoots i childBound a sp sp1 gens store memory domain limit
        annot good cell heapMem
    have memChild : memory (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i) =
        wordAddr conf child := by
      simpa only [childEq, BitVec.mul_comm] using memoryEq
    have inDomain : domain (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i) = true := by
      simpa only [BitVec.mul_comm] using domainEq
    refine ⟨getAddr conf ptr annot, addr, 0, ?_, addressEq, inDomain, ?_⟩
    · simpa only [wordAddr] using parentAddr.symm
    · refine ⟨heap, limit, a, sp, sp1, gens, heapMem, ?_, limitBound, spaceBound⟩
      refine ⟨child :: .pointer ptr annot :: rest, extended, ?_⟩
      exact .cons memChild.symm (.cons parentAddr restAddresses)

/-- The encoded child index selects a concrete block field and extends the
full memory relation with that child. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Block_MEM"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_blockMem {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List Value) (location : WordLocW width)
    (vars : List (Value × WordLocW width)) (i : Nat) (bound : i < values.length)
    (h : memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, location) :: vars) ∧
      goodDimindex width) :
    ∃ w addr offset : BitVec width,
      getRealOffset (smallnum (Int.ofNat i)) = some offset ∧
      location = .word w ∧ getRealAddr conf store w = some addr ∧ domain (addr + offset) = true ∧
      memoryRel conf bigEndian next refs space store memory domain
        ((values[i], memory (addr + offset)) :: (.block stamp tag values, location) :: vars) := by
  obtain ⟨w, addr, _, locationEq, addressEq, inDomain, extended⟩ :=
    memoryRel_elAny conf bigEndian next refs space store memory domain stamp tag values location vars i bound h
  let offset : BitVec width := StackRemove.bytesInWord width +
    BitVec.ofNat width i * StackRemove.bytesInWord width
  have encoded : (smallnum (Int.ofNat i) : BitVec width) = BitVec.ofNat width (4 * i) := by
    have nonneg : ¬ (Int.ofNat i < 0) := by
      rw [Int.ofNat_eq_natCast]
      exact Int.not_lt_of_ge (Int.natCast_nonneg i)
    simp only [smallnum, nonneg, ↓reduceIte]
    congr 1
  have offsetEq : getRealOffset (smallnum (Int.ofNat i) : BitVec width) = some offset := by
    rw [encoded]
    exact getRealOffset_thm i h.2
  have address : addr + offset = addr + StackRemove.bytesInWord width +
      StackRemove.bytesInWord width * BitVec.ofNat width i := by
    dsimp [offset]
    rw [BitVec.mul_comm, ← BitVec.add_assoc]
  refine ⟨w, addr, offset, offsetEq, locationEq, addressEq, ?_, ?_⟩
  · simpa only [address] using inDomain
  · simpa only [address] using extended

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
