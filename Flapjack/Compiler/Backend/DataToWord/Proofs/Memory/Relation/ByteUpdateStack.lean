import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateRefInv
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefEquality

/-! Preservation of the stack/reference invariant across byte-array updates. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Updating a referenced byte array and its heap cell preserves the full
stack/reference invariant when the head root identifies that cell. -/
theorem bcStackRefInv_byteUpdate {width : Nat} [NeZero width] (conf : Config) (next : Nat)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (roots : List (HeapAddress (WordLocW width))) (pre post : ValueHeap width)
    (be flag bit : Bool) (before after : List (BitVec 8)) (ptr : Nat)
    (sameLength : before.length = after.length)
    (found : sptLookup ptr refs = some (.byteArray flag before))
    (valid : bcStackRefInv conf next (.refPtr bit ptr :: stack) refs
      (.pointer (heapLength pre) (.word 0) :: roots,
        pre ++ [bytesRep be flag before (List.replicate (before.length / (width / 8) + 1) 0)] ++ post, be)) :
    bcStackRefInv conf next (.refPtr bit ptr :: stack)
      (sptInsert ptr (.byteArray flag after) refs)
      (.pointer (heapLength pre) (.word 0) :: roots,
        pre ++ [bytesRep be flag after (List.replicate (before.length / (width / 8) + 1) 0)] ++ post, be) := by
  obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, stackInv, refsInv⟩ := valid
  have headInv : valueInv conf (.refPtr bit ptr) refs
      (.pointer (heapLength pre) (.word 0), f, tf,
        pre ++ [bytesRep be flag before (List.replicate (before.length / (width / 8) + 1) 0)] ++ post) := by
    cases stackInv with
    | cons head _ => exact head
  rcases (valueInv_refPtr conf bit ptr refs _ f tf _).mp headInv with ordinary | thunk | inlined
  · obtain ⟨mapped, mappedLookup⟩ := ordinary.1
    have address := valueInv_byteRefAddress conf bit ptr refs _ f tf _ flag before found headInv
    have addressEq : heapLength pre = holFapply f ptr := (HeapAddress.pointer.inj address).1
    have ptrMap : f.lookup ptr = some (heapLength pre) := by
      rw [holFapply_of_lookup mappedLookup] at addressEq
      simpa [addressEq] using mappedLookup
    have shape := byteHeap_shape be flag before after (List.replicate (before.length / (width / 8) + 1) 0) pre post
    refine ⟨f, tf, mapInjInto_heapShape shape f injF, ?_, mapInjInto_heapShape shape tf injTf, ?_, nextBound, endian, ?_, ?_, ?_⟩
    · intro n domain
      by_cases same : n = ptr
      · subst n
        exact ⟨.byteArray flag after, sptLookup_sptInsert_same _ _ _⟩
      · obtain ⟨cell, cellFound⟩ := domainF n domain
        exact ⟨cell, by simpa [sptLookup_sptInsert_ne ptr n _ refs same] using cellFound⟩
    · intro n domain
      rw [allTimestamps_replaceByteArray refs (.refPtr bit ptr :: stack) ptr flag flag before after found]
      exact timestamps n domain
    · rw [allValues_replaceByteArray refs (.refPtr bit ptr :: stack) ptr flag flag before after found]
      exact unique
    · apply stackInv.imp
      intro value address related
      exact valueInv_byteUpdate conf value refs address f tf pre post be flag before after _ ptr flag before found related
    · intro n reachDomain
      apply bcRefInv_byteUpdate conf refs f tf pre post be flag before after ptr n sameLength found ptrMap injF
      apply refsInv n
      constructor
      · rw [← reachableRefs_replaceByteArray refs (.refPtr bit ptr :: stack) ptr flag flag before after found]
        exact reachDomain.1
      · exact reachDomain.2
  · obtain ⟨_, _, _, thunkFound, _⟩ := thunk
    rw [found] at thunkFound
    cases thunkFound
  · obtain ⟨_, thunkFound, _⟩ := inlined
    rw [found] at thunkFound
    cases thunkFound

/-- The abstract ML invariant survives updating a byte array; the theorem
also identifies the root and byte heap cell involved in the update. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "update_byte_ref_thm"
  (words_as_type_indexed_bitvec)]
theorem updateByteRef {width : Nat} [NeZero width] (conf : Config) (bit : Bool) (ptr : Nat)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : Flapjack.Compiler.Backend.GcCombined.GenState)
    (limit next : Nat) (flag : Bool) (before after : List (BitVec 8))
    (valid : absMlInv conf (.refPtr bit ptr :: stack) refs (roots, heap, be, a, sp, sp1, gens) limit next ∧
      sptLookup ptr refs = some (.byteArray flag before) ∧ before.length = after.length) :
    ∃ (roots2 : List (HeapAddress (WordLocW width))) (pre post : ValueHeap width) (words : List (BitVec width)),
      roots = .pointer (heapLength pre) (.word 0) :: roots2 ∧
      heap = pre ++ [bytesRep be flag before words] ++ post ∧
      words.length = before.length / (width / 8) + 1 ∧
      absMlInv conf (.refPtr bit ptr :: stack) (sptInsert ptr (.byteArray flag after) refs)
        (roots, pre ++ [bytesRep be flag after words] ++ post, be, a, sp, sp1, gens) limit next := by
  obtain ⟨⟨rootsOkOld, heapOkOld, gcOld, unusedOld, stackOld⟩, found, sameLength⟩ := valid
  obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, stackInv, refsInv⟩ := stackOld
  cases roots with
  | nil => cases stackInv
  | cons root roots2 =>
    have headInv : valueInv conf (.refPtr bit ptr) refs (root, f, tf, heap) := by
      cases stackInv with
      | cons head _ => exact head
    have headAddress := valueInv_byteRefAddress conf bit ptr refs root f tf heap flag before found headInv
    have domain : mapDomain f ptr := by
      rcases (valueInv_refPtr conf bit ptr refs root f tf heap).mp headInv with ordinary | thunk | inlined
      · exact ordinary.1
      · obtain ⟨_, _, _, thunkFound, _⟩ := thunk
        rw [found] at thunkFound
        cases thunkFound
      · obtain ⟨_, thunkFound, _⟩ := inlined
        rw [found] at thunkFound
        cases thunkFound
    have reach : reachableRefs (.refPtr bit ptr :: stack) refs ptr := by
      refine ⟨.refPtr bit ptr, ptr, by simp, by simp [getRefs], ?_⟩
      exact Relation.ReflTransGen.refl
    obtain ⟨mapped, mappedLookup⟩ := domain
    have refInv := refsInv ptr ⟨reach, ⟨mapped, mappedLookup⟩⟩
    have heapFound : heapLookup mapped heap = some (bytesRep be flag before
        (List.replicate (before.length / (width / 8) + 1) 0)) := by
      simpa [bcRefInv, mappedLookup, found] using refInv
    obtain ⟨pre, post, heapEq, mappedEq⟩ := heapLookup_split heap mapped _ heapFound
    have rootEq : root = .pointer (heapLength pre) (.word 0) := by
      rw [headAddress, holFapply_of_lookup mappedLookup, mappedEq]
    clear headAddress
    subst root
    subst heap
    simp only [List.append_assoc, List.singleton_append] at *
    have stackOld' : bcStackRefInv conf next (.refPtr bit ptr :: stack) refs
        (.pointer (heapLength pre) (.word 0) :: roots2,
          pre ++ [bytesRep be flag before (List.replicate (before.length / (width / 8) + 1) 0)] ++ post, be) := by
      simp only [List.append_assoc, List.singleton_append]
      exact ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, stackInv, refsInv⟩
    have shape := byteHeap_shape be flag before after (List.replicate (before.length / (width / 8) + 1) 0) pre post
    simp only [List.append_assoc, List.singleton_append] at shape
    refine ⟨roots2, pre, post, List.replicate (before.length / (width / 8) + 1) 0, rfl, rfl, by simp, ?_⟩
    refine ⟨rootsOk_shape _ shape rootsOkOld, heapOk_shape shape limit heapOkOld, ?_, ?_, ?_⟩
    · have gcShape := byteHeap_gcShape be flag before after (List.replicate (before.length / (width / 8) + 1) 0) pre post
      simp only [List.append_assoc, List.singleton_append] at gcShape
      exact gcKindInv_shape gcShape conf a sp sp1 gens gcOld
    · apply unusedSpaceInv_shape shape a (sp + sp1)
      exact unusedOld
    · simpa only [List.append_assoc, List.singleton_append] using
        bcStackRefInv_byteUpdate conf next stack refs roots2 pre post be flag bit before after ptr sameLength found stackOld'


end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
