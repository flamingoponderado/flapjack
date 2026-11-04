import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateStack

/-! Single-element reference-array updates. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Updating corresponding positions preserves a pairwise relation. -/
theorem forall2_set_pair {α β : Type} {rel : α → β → Prop}
    (xs : List α) (ys : List β) (index : Nat) (x : α) (y : β)
    (related : List.Forall₂ rel xs ys) (item : rel x y) :
    List.Forall₂ rel (xs.set index x) (ys.set index y) := by
  induction related generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => exact .cons item tail
    | succ index => exact .cons head (ih index)

/-- The reference-block contents exposed by a successful heap lookup. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_deref_def"]
def heapDeref {α β : Type} (address : Nat) (heap : List (HeapElement α (HeapTag × List β))) :
    Option (List (HeapAddress α)) :=
  match heapLookup address heap with
  | some (.dataElement pointers _ (.refTag, [])) => some pointers
  | _ => none

/-- A reference block dereferences to its pointer list. -/
theorem heapDeref_refBlock {α β : Type} (address : Nat)
    (heap : List (HeapElement α (HeapTag × List β))) (pointers : List (HeapAddress α))
    (found : heapLookup address heap = some (refBlock pointers)) :
    heapDeref address heap = some pointers := by
  simp [heapDeref, found, refBlock]


/-- Nonempty-prefix form used to prove the single-element update theorem. -/
theorem updateRefElementCore {width : Nat} [NeZero width] (conf : Config)
    (value : Flapjack.Compiler.Backend.DataSem.Value) (values stack : List Flapjack.Compiler.Backend.DataSem.Value) (bit : Bool) (ptr : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit next index : Nat)
    (old : List Flapjack.Compiler.Backend.DataSem.Value)
    (valid : absMlInv conf ((value :: values) ++ .refPtr bit ptr :: stack) refs (roots, heap, be, a, sp, sp1, gens) limit next ∧
      sptLookup ptr refs = some (.valueArray old) ∧ index < old.length) :
    ∃ (p : Nat) (rs roots2 oldRoots : List (HeapAddress (WordLocW width))) (firstRoot : HeapAddress (WordLocW width)) (heap2 : ValueHeap width) (u : WordLocW width),
      roots = rs ++ .pointer p u :: roots2 ∧ rs.head? = some firstRoot ∧ rs.length = (value :: values).length ∧ heapDeref p heap = some oldRoots ∧ heapLookup p heap = some (refBlock oldRoots) ∧ oldRoots.length = old.length ∧
      heapStore p [refBlock (oldRoots.set index firstRoot)] heap = (heap2, true) ∧
      absMlInv conf ((value :: values) ++ .refPtr bit ptr :: stack) (sptInsert ptr (.valueArray (old.set index value)) refs)
        (roots, heap2, be, a, sp, sp1, gens) limit next := by
  obtain ⟨⟨rootsValid, heapValid, gcValid, unused, stackInv⟩, found, indexBound⟩ := valid
  obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, related, refsInv⟩ := stackInv
  obtain ⟨rs, ptrRoot, roots2, rootsEq, prefixInv, pointerInv, tailInv⟩ :=
    forall2_split_head (value :: values) (.refPtr bit ptr) stack roots related
  have noThunk : ∀ mode value, sptLookup ptr refs ≠ some (.thunk mode value) := by
    intro mode value
    simp [found]
  obtain ⟨⟨p, pLookup⟩, _, ptrEq⟩ :=
    (valueInv_refPtr_notThunk conf bit ptr refs ptrRoot f tf heap noThunk).mp pointerInv
  have ptrEq' : ptrRoot = .pointer p (.word 0) := by
    simpa [holFapply_of_lookup pLookup, found, refPtrAnnot] using ptrEq
  have reachable : reachableRefs ((value :: values) ++ .refPtr bit ptr :: stack) refs ptr := by
    exact ⟨.refPtr bit ptr, ptr, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
  have ptrInv := refsInv ptr ⟨reachable, ⟨p, pLookup⟩⟩
  have oldCell : ∃ oldRoots, heapLookup p heap = some (refBlock oldRoots) ∧
      List.Forall₂ (fun addr value => valueInv conf value refs (addr, f, tf, heap)) oldRoots old := by
    simpa [bcRefInv, pLookup, found] using ptrInv
  obtain ⟨oldRoots, oldLookup, oldInv⟩ := oldCell
  obtain ⟨pre, post, heapEq, pEq⟩ := heapLookup_split heap p _ oldLookup
  cases rs with
  | nil => cases prefixInv
  | cons firstRoot restRoots =>
    have firstInv : valueInv conf value refs (firstRoot, f, tf, heap) := by
      cases prefixInv with
      | cons head _ => exact head
    have equalLengths : oldRoots.length = (oldRoots.set index firstRoot).length := by simp
    rw [ptrEq'] at rootsEq
    subst roots
    subst p
    subst heap
    let newHeap := pre ++ refBlock (oldRoots.set index firstRoot) :: post
    let newRefs := sptInsert ptr (.valueArray (old.set index value)) refs
    let keep := allTimestamps newRefs ((value :: values) ++ .refPtr bit ptr :: stack)
    let tf2 := restrictTimestampMap tf keep
    have heapInv : refBlockInv (pre ++ refBlock oldRoots :: post) newHeap := by
      simpa [newHeap, List.append_assoc] using refBlockInv_replace pre post oldRoots (oldRoots.set index firstRoot) equalLengths
    have ptrMap : f.lookup ptr = some (heapLength pre) := pLookup
    have valuesInv : List.Forall₂ (fun value addr => valueInv conf value refs (addr, f, tf, pre ++ refBlock oldRoots :: post))
        (old.set index value) (oldRoots.set index firstRoot) :=
      forall2_set_pair old oldRoots index value firstRoot oldInv.flip firstInv
    have newRoots : ∀ addr ∈ oldRoots.set index firstRoot,
        addr ∈ (firstRoot :: restRoots) ++ .pointer (heapLength pre) (.word 0) :: roots2 ∨ addr ∈ oldRoots := by
      intro addr member
      rcases List.mem_or_eq_of_mem_set member with oldMember | same
      · exact Or.inr oldMember
      · subst addr
        exact Or.inl (by simp)
    have heapComponents := refBlockReplace_heapInvariants conf pre post
      ((firstRoot :: restRoots) ++ .pointer (heapLength pre) (.word 0) :: roots2) oldRoots (oldRoots.set index firstRoot) a sp sp1 limit gens equalLengths
      (by simpa [List.append_assoc] using rootsValid) (by simpa [List.append_assoc] using heapValid)
      (by simpa [List.append_assoc] using gcValid) (by simpa [List.append_assoc] using unused)
      newRoots
    have dataEq (n : Nat) : isSomeDataElement (heapLookup n (pre ++ refBlock oldRoots :: post)) ↔
        isSomeDataElement (heapLookup n newHeap) := by
      simpa [newHeap, List.append_assoc] using refBlock_replace_isSomeData pre post oldRoots (oldRoots.set index firstRoot) equalLengths n
    have injFNew : mapInjInto f (fun n => isSomeDataElement (heapLookup n newHeap)) :=
      ⟨fun n domain => (dataEq _).mp (injF.1 n domain), injF.2⟩
    have injTfNew : mapInjInto tf2 (fun n => isSomeDataElement (heapLookup n newHeap)) := by
      simpa [tf2, newHeap, List.append_assoc] using mapInjInto_arrayUpdate_restrict tf keep pre post oldRoots (oldRoots.set index firstRoot) equalLengths
        (by simpa [List.append_assoc] using injTf)
    have stackNew : List.Forall₂ (fun value addr => valueInv conf value newRefs (addr, f, tf2, newHeap))
        ((value :: values) ++ .refPtr bit ptr :: stack) ((firstRoot :: restRoots) ++ .pointer (heapLength pre) (.word 0) :: roots2) := by
      simpa [newRefs, tf2, keep, newHeap, List.append_assoc] using
        valueListInv_arrayUpdate_restrict conf refs ptr old (old.set index value) ((value :: values) ++ .refPtr bit ptr :: stack)
          ((firstRoot :: restRoots) ++ .pointer (heapLength pre) (.word 0) :: roots2) f tf _ _ found heapInv related
    have uniqueNew : blocksUnique next (allValues newRefs ((value :: values) ++ .refPtr bit ptr :: stack)) :=
      blocksUnique_updateRef_set next refs (value :: values) (.refPtr bit ptr :: stack) old ptr index value found (by simp) unique
    have refsNew : ∀ n, reachableRefs ((value :: values) ++ .refPtr bit ptr :: stack) newRefs n ∧ mapDomain f n →
        bcRefInv conf n newRefs (f, tf2, newHeap, be) := by
      intro n ⟨reachNew, domain⟩
      have reachOld := reachableRefs_updateValueArray_set refs (value :: values) stack old ptr index bit value found (by simp) n reachNew
      have oldRef := refsInv n ⟨reachOld, domain⟩
      simpa [newRefs, tf2, keep, newHeap, List.append_assoc] using
        bcRefInv_arrayUpdate conf refs f tf pre post oldRoots (oldRoots.set index firstRoot) be ptr n old (old.set index value)
          ((value :: values) ++ .refPtr bit ptr :: stack) equalLengths found ptrMap (by simpa [List.append_assoc] using injF)
          (by simpa [List.append_assoc] using valuesInv) (by simpa [List.append_assoc] using oldRef)
    have stackNewInv : bcStackRefInv conf next ((value :: values) ++ .refPtr bit ptr :: stack) newRefs
        ((firstRoot :: restRoots) ++ .pointer (heapLength pre) (.word 0) :: roots2, newHeap, be) := by
      refine ⟨f, tf2, injFNew, ?_, injTfNew, ?_, ?_, endian, uniqueNew, stackNew, refsNew⟩
      · intro n domain
        by_cases same : n = ptr
        · subst n
          exact ⟨.valueArray (old.set index value), sptLookup_sptInsert_same _ _ _⟩
        · obtain ⟨cell, oldCell⟩ := domainF n domain
          exact ⟨cell, by simpa [newRefs, sptLookup_sptInsert_ne ptr n _ refs same] using oldCell⟩
      · intro n domain
        obtain ⟨v, lookup⟩ := domain
        exact ((restrictTimestampMap_lookup_some tf keep n v).mp lookup).1
      · intro n domain
        exact nextBound n (restrictTimestampMap_domain_apply tf keep n domain).1
    refine ⟨heapLength pre, firstRoot :: restRoots, roots2, oldRoots, firstRoot, newHeap, .word 0, rfl, rfl, ?_, ?_, oldLookup, ?_, ?_, ?_⟩
    · exact prefixInv.length_eq.symm
    · exact heapDeref_refBlock _ _ _ oldLookup
    · exact oldInv.length_eq
    · simpa [newHeap, List.append_assoc] using heapStore_refBlock pre post (oldRoots.set index firstRoot) oldRoots equalLengths.symm
    · exact ⟨by simpa [newHeap, List.append_assoc] using heapComponents.1,
        by simpa [newHeap, List.append_assoc] using heapComponents.2.1,
        by simpa [newHeap, List.append_assoc] using heapComponents.2.2.1,
        by simpa [newHeap, List.append_assoc] using heapComponents.2.2.2, stackNewInv⟩

/-- Updating one value-array element preserves the abstract invariant and
identifies both the old reference contents and the successful heap store.
The defaults in the two `headD` expressions are unreachable because the
source prefix is nonempty and the root prefix has the same length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "update_ref_thm1"
  (words_as_type_indexed_bitvec)]
theorem updateRefElement {width : Nat} [NeZero width] (conf : Config)
    (values stack : List Flapjack.Compiler.Backend.DataSem.Value) (bit : Bool) (ptr : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit next index : Nat)
    (old : List Flapjack.Compiler.Backend.DataSem.Value)
    (valid : absMlInv conf (values ++ .refPtr bit ptr :: stack) refs (roots, heap, be, a, sp, sp1, gens) limit next ∧
      sptLookup ptr refs = some (.valueArray old) ∧ index < old.length ∧ 0 < values.length) :
    ∃ (p : Nat) (rs roots2 oldRoots : List (HeapAddress (WordLocW width))) (heap2 : ValueHeap width) (u : WordLocW width),
      roots = rs ++ .pointer p u :: roots2 ∧ rs.length = values.length ∧
      heapDeref p heap = some oldRoots ∧ oldRoots.length = old.length ∧
      heapStore p [refBlock (oldRoots.set index (rs.headD (.pointer 0 (.word 0))))] heap = (heap2, true) ∧
      absMlInv conf (values ++ .refPtr bit ptr :: stack)
        (sptInsert ptr (.valueArray (old.set index (values.headD (.number 0)))) refs)
        (roots, heap2, be, a, sp, sp1, gens) limit next := by
  obtain ⟨invariant, found, indexBound, nonempty⟩ := valid
  cases values with
  | nil => simp at nonempty
  | cons value values =>
    obtain ⟨p, rs, roots2, oldRoots, firstRoot, heap2, u, rootsEq, headEq, lengthEq, deref, _, oldLength, stored, updated⟩ :=
      updateRefElementCore conf value values stack bit ptr refs roots heap be a sp sp1 gens limit next index old
        ⟨invariant, found, indexBound⟩
    cases rs with
    | nil => simp at headEq
    | cons root rest =>
      simp only [List.head?_cons, Option.some.injEq] at headEq
      subst root
      exact ⟨p, firstRoot :: rest, roots2, oldRoots, heap2, u, rootsEq, lengthEq, deref, oldLength, stored, updated⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
