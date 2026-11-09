module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueArray
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack

@[expose] public section

/-! Concrete payload reads for value-array references. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Lean-side separation helper: a value-array child occupies its payload address. -/
theorem wordHeap_refElement {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index : Nat) (roots : List (HeapAddress (WordLocW width)))
    (i : Nat) (bound : i < roots.length) (curr : BitVec width)
    (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (refBlock roots))
    (heapAssertion : wordHeap curr heap conf whole) :
    whole (curr + StackRemove.bytesInWord width * BitVec.ofNat width index +
      StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width,
      wordAddr conf roots[i]) := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index (refBlock roots) found
  subst heap
  subst index
  rw [wordHeapAppend] at heapAssertion
  obtain ⟨prefixHeap, restHeap, split1, _, restAssertion⟩ := heapAssertion
  change SetSep.star (wordEl _ (refBlock roots) conf) (wordHeap _ after conf) restHeap at restAssertion
  obtain ⟨elementHeap, suffixHeap, split2, elementAssertion, _⟩ := restAssertion
  simp only [wordEl, refBlock, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map] at elementAssertion
  obtain ⟨listHeap, pureHeap, split3, listAssertion, _⟩ := elementAssertion
  obtain ⟨singleton, tailHeap, split4, _, tailAssertion⟩ := listAssertion
  let start := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before)
  let cell := (start + StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width,
    wordAddr conf roots[i])
  have tailMember : tailHeap cell := by
    have h := wordList_indexMember (roots.map (wordAddr conf)) i (by simpa using bound)
      (start + StackRemove.bytesInWord width) tailHeap tailAssertion
    simpa only [List.getElem_map] using h
  have listMember : listHeap cell := by
    rw [← split4.1]
    exact Or.inr tailMember
  have elementMember : elementHeap cell := by
    rw [← split3.1]
    exact Or.inl listMember
  have restMember : restHeap cell := by
    rw [← split2.1]
    exact Or.inl elementMember
  have wholeMember : whole cell := by
    rw [← split1.1]
    exact Or.inr restMember
  exact wholeMember

/-- Lean-side separation helper: an array child is readable at its decoded
address plus the header and element offset. -/
theorem heapInMemoryStore_refElement {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index : Nat) (roots : List (HeapAddress (WordLocW width)))
    (i : Nat) (bound : i < roots.length) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (limit : Nat)
    (annot : WordLocW width) (good : goodDimindex width)
    (found : heapLookup index heap = some (refBlock roots))
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ addr : BitVec width,
      getRealAddr conf store (getAddr conf index annot) = some addr ∧
      getRealSimpleAddr conf store (getAddr conf index annot) = some addr ∧
      memory (addr + StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width) =
        wordAddr conf roots[i] ∧
      domain (addr + StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width) = true := by
  have heapBound := heapMem.1
  obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
  obtain ⟨active, inactive, split, activeHeap, _⟩ := heapAssertion
  have activeMember := wordHeap_refElement conf heap index roots i bound curr active found activeHeap
  have graph : SetSep.fun2Set (memory, fun addr => domain addr = true)
      (curr + StackRemove.bytesInWord width * BitVec.ofNat width index +
       StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width,
       wordAddr conf roots[i]) := by
    rw [← split.1]
    exact Or.inl activeMember
  have facts := (SetSep.fun2SetThm memory (fun addr => domain addr = true) _ (wordAddr conf roots[i])).mp graph
  have addr := getRealAddr_getAddr conf store heap index (refBlock roots) curr annot
    ⟨heapBound, found, stored, good⟩
  refine ⟨curr + StackRemove.bytesInWord width * BitVec.ofNat width index, ?_, ?_, facts.1, facts.2⟩
  · simpa only [BitVec.mul_comm] using addr.2
  · simpa only [BitVec.mul_comm] using addr.1

/-- Lean-side invariant helper: values reachable after pushing an array element
were already in the original invariant, including nested blocks. -/
theorem allValues_refArrayChildSubset (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (ptr : Nat) (values : List Value) (child value : Value)
    (found : sptLookup ptr refs = some (.valueArray values)) (member : child ∈ values) :
    allValues refs (child :: stack) value → allValues refs stack value := by
  intro h
  rcases h with inArray | inThunk | inMut | inStack
  · exact Or.inl inArray
  · exact Or.inr (Or.inl inThunk)
  · exact Or.inr (Or.inr (Or.inl inMut))
  · have split : valueListValues (child :: stack) = valueListValues [child] ++ valueListValues stack := by
      simpa using valueListValues_append [child] stack
    rw [split, List.mem_append] at inStack
    rcases inStack with inChild | old
    · exact Or.inl ⟨ptr, values, found, valueListValues_singleton_subset values child value member inChild⟩
    · exact Or.inr (Or.inr (Or.inr old))

/-- Lean-side invariant helper: pushing a value-array element preserves block uniqueness. -/
theorem blocksUnique_refArrayChild (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (ptr : Nat) (values : List Value) (i : Nat) (next : Nat)
    (found : sptLookup ptr refs = some (.valueArray values)) (bound : i < values.length)
    (unique : blocksUnique next (allValues refs stack)) :
    blocksUnique next (allValues refs (values[i] :: stack)) := by
  intro stamp tag1 xs1 tag2 xs2 ⟨first, ne1, second, ne2⟩
  exact unique stamp tag1 xs1 tag2 xs2
    ⟨allValues_refArrayChildSubset refs stack ptr values values[i] _ found (List.getElem_mem bound) first,
      ne1, allValues_refArrayChildSubset refs stack ptr values values[i] _ found (List.getElem_mem bound) second, ne2⟩

/-- Exposing an array reference's in-bounds child preserves the abstract ML
heap invariant. This is Lean-side invariant infrastructure. -/
theorem absMlInv_refArrayChild {width : Nat} [NeZero width] (conf : Config)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit next : Nat)
    (bit : Bool) (ref : Nat) (values : List Value) (i : Nat) (bound : i < values.length)
    (found : sptLookup ref refs = some (.valueArray values))
    (inv : absMlInv conf (.refPtr bit ref :: stack) refs
      (roots, heap, bigEndian, a, sp, sp1, gens) limit next) :
    ∃ (parentRoot childRoot : HeapAddress (WordLocW width)) (rest : List (HeapAddress (WordLocW width)))
      (ptr : Nat) (childRoots : List (HeapAddress (WordLocW width)))
      (childBound : i < childRoots.length),
      roots = parentRoot :: rest ∧ parentRoot = .pointer ptr (.word 0) ∧
      heapLookup ptr heap = some (refBlock childRoots) ∧ childRoot = childRoots[i] ∧
      absMlInv conf (values[i] :: .refPtr bit ref :: stack) refs
        (childRoot :: roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  obtain ⟨rootOk, heapOk', gc, unused, stackInv⟩ := inv
  obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimestamps, tfBound, endian, unique, related, cells⟩ := stackInv
  cases roots with
  | nil => cases related
  | cons parentRoot rest =>
    cases related with
    | cons parentRelated remaining =>
      have noThunk : ∀ mode value, sptLookup ref refs ≠ some (.thunk mode value) := by
        intro mode value eq
        rw [found] at eq
        cases eq
      obtain ⟨domainF, _, rootEq⟩ :=
        (valueInv_refPtr_notThunk conf bit ref refs parentRoot f tf heap noThunk).mp parentRelated
      obtain ⟨ptr, ffound⟩ := domainF
      rw [found, holFapply_of_lookup ffound] at rootEq
      have parentEq : parentRoot = .pointer ptr (.word 0) := by simpa [refPtrAnnot] using rootEq
      have reachable : reachableRefs (.refPtr bit ref :: stack) refs ref := by
        exact ⟨.refPtr bit ref, ref, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
      have cellInv := cells ref ⟨reachable, ⟨ptr, ffound⟩⟩
      obtain ⟨childRoots, cell, pair⟩ : ∃ children, heapLookup ptr heap = some (refBlock children) ∧
          List.Forall₂ (fun address value => valueInv conf value refs (address, f, tf, heap)) children values := by
        simpa [bcRefInv, ffound, found] using cellInv
      have childBound : i < childRoots.length := by rw [pair.length_eq]; exact bound
      have childRelated := pair.get childBound bound
      have childMember : values[i] ∈ values := List.getElem_mem bound
      have childValues : allValues refs (.refPtr bit ref :: stack) values[i] := by
        exact Or.inl ⟨ref, values, found, mem_valueListValues values values[i] childMember⟩
      refine ⟨parentRoot, childRoots[i], rest, ptr, childRoots, childBound, rfl, parentEq, cell, rfl, ?_⟩
      refine ⟨?_, heapOk', gc, unused, ?_⟩
      · intro target annotation member
        rcases List.mem_cons.mp member with eq | old
        · have inChildren : HeapAddress.pointer target annotation ∈ childRoots := by
            rw [eq]
            exact List.getElem_mem childBound
          apply heapOk'.2.2 childRoots childRoots.length (.refTag, []) target annotation
          refine ⟨?_, inChildren⟩
          simpa only [refBlock] using heapLookup_mem heap ptr (refBlock childRoots) cell
        · exact rootOk target annotation old
      · refine ⟨f, tf, fInj, fDomain, tfInj, ?_, tfBound, endian, ?_, ?_, ?_⟩
        · intro ts dom
          rw [← allTimestamps_headEq values[i] refs (.refPtr bit ref :: stack) () childValues]
          exact tfTimestamps ts dom
        · exact blocksUnique_refArrayChild refs (.refPtr bit ref :: stack) ref values i next found bound unique
        · exact .cons childRelated (.cons parentRelated remaining)
        · intro n ⟨reachableNew, dom⟩
          apply cells n
          refine ⟨?_, dom⟩
          obtain ⟨root, start, inStack, inRefs, path⟩ := reachableNew
          rcases List.mem_cons.mp inStack with eq | old
          · subst root
            refine ⟨.refPtr bit ref, ref, by simp, by simp [getRefs], ?_⟩
            have edge : refEdge refs ref start := by
              simp [refEdge, found, getRefs, List.mem_flatMap]
              exact ⟨values[i], childMember, inRefs⟩
            exact Relation.ReflTransGen.head edge path
          · exact ⟨root, start, old, inRefs, path⟩

/-- Reading a value-array element gives the concrete payload word and extends
the full memory relation with the corresponding source value. This is
Lean-side infrastructure for the array case of field access. -/
theorem memoryRel_refArrayElement {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bit : Bool) (ref : Nat) (values : List Value) (location : WordLocW width)
    (vars : List (Value × WordLocW width)) (i : Nat) (bound : i < values.length)
    (found : sptLookup ref refs = some (.valueArray values))
    (h : memoryRel conf bigEndian next refs space store memory domain ((.refPtr bit ref, location) :: vars) ∧
      goodDimindex width) :
    ∃ w addr : BitVec width,
      location = .word w ∧ getRealAddr conf store w = some addr ∧ getRealSimpleAddr conf store w = some addr ∧
      domain (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i) = true ∧
      memoryRel conf bigEndian next refs space store memory domain
        ((values[i], memory (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i)) ::
          (.refPtr bit ref, location) :: vars) := by
  obtain ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩, good⟩ := h
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  obtain ⟨parent, child, rest, ptr, childRoots, childBound, rootsEq, parentEq, cell, childEq, extended⟩ :=
    absMlInv_refArrayChild conf (vars.map Prod.fst) refs roots heap bigEndian a sp sp1 gens limit next
      bit ref values i bound found absInv
  subst roots
  cases addresses with
  | cons parentAddr restAddresses =>
    subst parent
    obtain ⟨addr, addressEq, simpleEq, memoryEq, domainEq⟩ :=
      heapInMemoryStore_refElement conf heap ptr childRoots i childBound a sp sp1 gens store memory domain limit
        (.word 0) good cell heapMem
    have memChild : memory (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i) =
        wordAddr conf child := by
      simpa only [childEq, BitVec.mul_comm] using memoryEq
    have inDomain : domain (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i) = true := by
      simpa only [BitVec.mul_comm] using domainEq
    refine ⟨getAddr conf ptr (.word 0), addr, ?_, addressEq, simpleEq, inDomain, ?_⟩
    · simpa only [wordAddr] using parentAddr.symm
    · refine ⟨heap, limit, a, sp, sp1, gens, heapMem, ?_, limitBound, spaceBound⟩
      refine ⟨child :: .pointer ptr (.word 0) :: rest, extended, ?_⟩
      exact .cons memChild.symm (.cons parentAddr restAddresses)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
