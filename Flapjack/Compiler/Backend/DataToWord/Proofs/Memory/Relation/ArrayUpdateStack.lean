import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateRestriction

/-! Abstract value-array updates in the data-to-word memory invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Replacing an entire value-array reference by the values at the front of
the stack preserves the abstract ML invariant and returns the new heap. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "update_ref_thm"
  (words_as_type_indexed_bitvec)]
theorem updateRef {width : Nat} [NeZero width] (conf : Config)
    (values stack : List Flapjack.Compiler.Backend.DataSem.Value) (bit : Bool) (ptr : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit next : Nat)
    (old : List Flapjack.Compiler.Backend.DataSem.Value)
    (valid : absMlInv conf (values ++ .refPtr bit ptr :: stack) refs (roots, heap, be, a, sp, sp1, gens) limit next ∧
      sptLookup ptr refs = some (.valueArray old) ∧ values.length = old.length) :
    ∃ (p : Nat) (rs roots2 : List (HeapAddress (WordLocW width))) (heap2 : ValueHeap width) (u : WordLocW width),
      roots = rs ++ .pointer p u :: roots2 ∧ heapStore p [refBlock rs] heap = (heap2, true) ∧
      absMlInv conf (values ++ .refPtr bit ptr :: stack) (sptInsert ptr (.valueArray values) refs)
        (roots, heap2, be, a, sp, sp1, gens) limit next := by
  obtain ⟨⟨rootsValid, heapValid, gcValid, unused, stackInv⟩, found, sameValues⟩ := valid
  obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, related, refsInv⟩ := stackInv
  obtain ⟨rs, ptrRoot, roots2, rootsEq, prefixInv, pointerInv, tailInv⟩ :=
    forall2_split_head values (.refPtr bit ptr) stack roots related
  have noThunk : ∀ mode value, sptLookup ptr refs ≠ some (.thunk mode value) := by
    intro mode value
    simp [found]
  obtain ⟨⟨p, pLookup⟩, _, ptrEq⟩ :=
    (valueInv_refPtr_notThunk conf bit ptr refs ptrRoot f tf heap noThunk).mp pointerInv
  have ptrEq' : ptrRoot = .pointer p (.word 0) := by
    simpa [holFapply_of_lookup pLookup, found, refPtrAnnot] using ptrEq
  have reachable : reachableRefs (values ++ .refPtr bit ptr :: stack) refs ptr := by
    exact ⟨.refPtr bit ptr, ptr, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
  have ptrInv := refsInv ptr ⟨reachable, ⟨p, pLookup⟩⟩
  have oldCell : ∃ oldRoots, heapLookup p heap = some (refBlock oldRoots) ∧
      List.Forall₂ (fun addr value => valueInv conf value refs (addr, f, tf, heap)) oldRoots old := by
    simpa [bcRefInv, pLookup, found] using ptrInv
  obtain ⟨oldRoots, oldLookup, oldInv⟩ := oldCell
  obtain ⟨pre, post, heapEq, pEq⟩ := heapLookup_split heap p _ oldLookup
  have equalLengths : oldRoots.length = rs.length := by
    have h1 := oldInv.length_eq
    have h2 := prefixInv.length_eq
    omega
  rw [ptrEq'] at rootsEq
  subst roots
  subst p
  subst heap
  let newHeap := pre ++ refBlock rs :: post
  let newRefs := sptInsert ptr (.valueArray values) refs
  let keep := allTimestamps newRefs (values ++ .refPtr bit ptr :: stack)
  let tf2 := restrictTimestampMap tf keep
  have heapInv : refBlockInv (pre ++ refBlock oldRoots :: post) newHeap := by
    simpa [newHeap, List.append_assoc] using refBlockInv_replace pre post oldRoots rs equalLengths
  have ptrMap : f.lookup ptr = some (heapLength pre) := pLookup
  have valuesInv : List.Forall₂ (fun value addr => valueInv conf value refs (addr, f, tf, pre ++ refBlock oldRoots :: post)) values rs := prefixInv
  have newRoots : ∀ addr ∈ rs, addr ∈ rs ++ .pointer (heapLength pre) (.word 0) :: roots2 := by
    intro addr member
    exact List.mem_append_left _ member
  have heapComponents := refBlockReplace_heapInvariants conf pre post
    (rs ++ .pointer (heapLength pre) (.word 0) :: roots2) oldRoots rs a sp sp1 limit gens equalLengths
    (by simpa [List.append_assoc] using rootsValid) (by simpa [List.append_assoc] using heapValid)
    (by simpa [List.append_assoc] using gcValid) (by simpa [List.append_assoc] using unused) newRoots
  have dataEq (n : Nat) : isSomeDataElement (heapLookup n (pre ++ refBlock oldRoots :: post)) ↔
      isSomeDataElement (heapLookup n newHeap) := by
    simpa [newHeap, List.append_assoc] using refBlock_replace_isSomeData pre post oldRoots rs equalLengths n
  have injFNew : mapInjInto f (fun n => isSomeDataElement (heapLookup n newHeap)) :=
    ⟨fun n domain => (dataEq _).mp (injF.1 n domain), injF.2⟩
  have injTfNew : mapInjInto tf2 (fun n => isSomeDataElement (heapLookup n newHeap)) := by
    simpa [tf2, newHeap, List.append_assoc] using mapInjInto_arrayUpdate_restrict tf keep pre post oldRoots rs equalLengths
      (by simpa [List.append_assoc] using injTf)
  have stackNew : List.Forall₂ (fun value addr => valueInv conf value newRefs (addr, f, tf2, newHeap))
      (values ++ .refPtr bit ptr :: stack) (rs ++ .pointer (heapLength pre) (.word 0) :: roots2) := by
    simpa [newRefs, tf2, keep, newHeap, List.append_assoc] using
      valueListInv_arrayUpdate_restrict conf refs ptr old values (values ++ .refPtr bit ptr :: stack)
        (rs ++ .pointer (heapLength pre) (.word 0) :: roots2) f tf _ _ found heapInv related
  have uniqueNew : blocksUnique next (allValues newRefs (values ++ .refPtr bit ptr :: stack)) :=
    blocksUnique_updateRef next refs values bit ptr stack unique
  have refsNew : ∀ n, reachableRefs (values ++ .refPtr bit ptr :: stack) newRefs n ∧ mapDomain f n →
      bcRefInv conf n newRefs (f, tf2, newHeap, be) := by
    intro n ⟨reachNew, domain⟩
    have reachOld := reachableRefs_updateValueArray refs values stack ptr bit n reachNew
    have oldRef := refsInv n ⟨reachOld, domain⟩
    simpa [newRefs, tf2, keep, newHeap, List.append_assoc] using
      bcRefInv_arrayUpdate conf refs f tf pre post oldRoots rs be ptr n old values
        (values ++ .refPtr bit ptr :: stack) equalLengths found ptrMap (by simpa [List.append_assoc] using injF)
        (by simpa [List.append_assoc] using valuesInv) (by simpa [List.append_assoc] using oldRef)
  have stackNewInv : bcStackRefInv conf next (values ++ .refPtr bit ptr :: stack) newRefs
      (rs ++ .pointer (heapLength pre) (.word 0) :: roots2, newHeap, be) := by
    refine ⟨f, tf2, injFNew, ?_, injTfNew, ?_, ?_, endian, uniqueNew, stackNew, refsNew⟩
    · intro n domain
      by_cases same : n = ptr
      · subst n
        exact ⟨.valueArray values, sptLookup_sptInsert_same _ _ _⟩
      · obtain ⟨cell, oldCell⟩ := domainF n domain
        exact ⟨cell, by simpa [newRefs, sptLookup_sptInsert_ne ptr n _ refs same] using oldCell⟩
    · intro n domain
      obtain ⟨v, lookup⟩ := domain
      exact ((restrictTimestampMap_lookup_some tf keep n v).mp lookup).1
    · intro n domain
      exact nextBound n (restrictTimestampMap_domain_apply tf keep n domain).1
  refine ⟨heapLength pre, rs, roots2, newHeap, .word 0, rfl, ?_, ?_⟩
  · simpa [newHeap, List.append_assoc] using heapStore_refBlock pre post rs oldRoots equalLengths.symm
  · exact ⟨by simpa [newHeap, List.append_assoc] using heapComponents.1,
      by simpa [newHeap, List.append_assoc] using heapComponents.2.1,
      by simpa [newHeap, List.append_assoc] using heapComponents.2.2.1,
      by simpa [newHeap, List.append_assoc] using heapComponents.2.2.2, stackNewInv⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
