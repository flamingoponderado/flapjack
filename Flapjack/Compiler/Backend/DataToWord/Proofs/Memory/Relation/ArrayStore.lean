import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateElement
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefArrayElement

/-! Concrete stores to value-array reference blocks. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Replacing one encoded reference-block payload word preserves its header
and any disjoint memory frame. -/
theorem wordEl_refStore {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (pointers : List (HeapAddress (WordLocW width))) (replacement : HeapAddress (WordLocW width))
    (base : BitVec width) (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (index : Nat)
    (bound : index < pointers.length)
    (separated : SetSep.star (wordEl base (refBlock pointers) conf) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    domain (base + StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width) = true ∧
    SetSep.star (wordEl base (refBlock (pointers.set index replacement)) conf) frame
      (SetSep.fun2Set ((fun key => if key = base + StackRemove.bytesInWord width +
        BitVec.ofNat width index * StackRemove.bytesInWord width then wordAddr conf replacement else memory key),
        fun addr => domain addr = true)) := by
  simp only [wordEl, refBlock, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map,
    Misc.wordList, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  have inGraph : SetSep.fun2Set (memory, fun addr => domain addr = true)
      (base + StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width,
        wordAddr conf pointers[index]) := by
    obtain ⟨payload, rest, split, words, _⟩ := separated
    rw [← split.1]
    left
    have member := wordList_indexMember (pointers.map (wordAddr conf)) index
      (by simpa using bound) (base + StackRemove.bytesInWord width) payload words
    simpa [List.getElem_map] using member
  have inDomain := ((SetSep.fun2SetThm memory (fun addr => domain addr = true) _ _).mp inGraph).2
  have changed := wordList_write (base + StackRemove.bytesInWord width) (pointers.map (wordAddr conf)) index
    (wordAddr conf replacement) memory (fun addr => domain addr = true) _ (by simpa using bound) separated
  rw [star_swap_first] at changed
  refine ⟨inDomain, ?_⟩
  simpa [wordEl, refBlock, wordPayload, List.map_set, Misc.wordList, ← SetSep.starAssoc] using changed

/-- A value-array element store preserves the surrounding word heap and an
arbitrary separated frame. -/
theorem wordHeap_refStore {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (pointers : List (HeapAddress (WordLocW width))) (replacement : HeapAddress (WordLocW width))
    (curr : BitVec width) (pre post : ValueHeap width) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (index : Nat) (bound : index < pointers.length)
    (separated : SetSep.star (wordHeap curr (pre ++ [refBlock pointers] ++ post) conf) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    let addr := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
      StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width
    domain addr = true ∧
    SetSep.star (wordHeap curr (pre ++ [refBlock (pointers.set index replacement)] ++ post) conf) frame
      (SetSep.fun2Set ((fun key => if key = addr then wordAddr conf replacement else memory key),
        fun addr => domain addr = true)) := by
  rw [List.append_assoc, wordHeapAppend] at separated
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  obtain ⟨inDomain, result⟩ := wordEl_refStore conf pointers replacement
    (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)) memory domain _ index bound separated
  refine ⟨inDomain, ?_⟩
  rw [star_swap_first] at result
  rw [List.append_assoc, wordHeapAppend]
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc]
  simpa [refBlock, elLength] using result

/-- Updating a reference-block payload preserves both heaps and the
heap/store invariant, and identifies the concrete store address. -/
theorem heapInMemoryStore_refStore {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (pointers : List (HeapAddress (WordLocW width))) (replacement : HeapAddress (WordLocW width))
    (pre post : ValueHeap width) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (limit index : Nat) (bound : index < pointers.length)
    (heapMem : heapInMemoryStore (pre ++ [refBlock pointers] ++ post)
      a sp sp1 gens conf store memory domain limit) :
    ∃ curr, store.lookup .currHeap = some (.word curr) ∧
      let addr := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
        StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width
      domain addr = true ∧
      heapInMemoryStore (pre ++ [refBlock (pointers.set index replacement)] ++ post)
        a sp sp1 gens conf store (fun key => if key = addr then wordAddr conf replacement else memory key) domain limit := by
  obtain ⟨bound1, bound2, shift, lenNonzero, lenBound, shiftBound, globals,
    curr, other, currAligned, otherAligned, currStore, otherStore, nextStore,
    triggerStore, endStore, lengthStore, globInv, genInv, separated⟩ := heapMem
  obtain ⟨inDomain, heapNew⟩ := wordHeap_refStore conf pointers replacement curr pre post memory domain _ index bound separated
  have lengthEq : heapLength (pre ++ [refBlock pointers] ++ post) =
      heapLength (pre ++ [refBlock (pointers.set index replacement)] ++ post) := by
    simp [heapLength, List.map_append, List.sum_append, refBlock, elLength]
  refine ⟨curr, currStore, inDomain, ?_⟩
  refine ⟨?_, ?_, shift, lenNonzero, lenBound, shiftBound, globals, curr, other, currAligned, otherAligned,
    currStore, otherStore, nextStore, triggerStore, endStore, lengthStore, globInv, genInv, heapNew⟩
  · simpa only [← lengthEq] using bound1
  · simpa only [← lengthEq] using bound2

/-- Updating an in-range reference-array element preserves the complete
memory relation after the concrete word store. -/
theorem memoryRel_refStore {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (value : DataSem.Value) (word : WordLocW width)
    (bit : Bool) (ptr : Nat) (root : WordLocW width) (vars : List (DataSem.Value × WordLocW width))
    (old : List DataSem.Value) (index : Nat) (found : sptLookup ptr refs = some (.valueArray old))
    (bound : index < old.length) (good : goodDimindex width)
    (related : memoryRel conf be next refs space store memory domain ((value, word) :: (.refPtr bit ptr, root) :: vars)) :
    ∃ ptrWord addr, root = .word ptrWord ∧ getRealAddr conf store ptrWord = some addr ∧
      let target := addr + StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width
      domain target = true ∧
      memoryRel conf be next (sptInsert ptr (.valueArray (old.set index value)) refs) space store
        (fun key => if key = target then word else memory key) domain ((value, word) :: (.refPtr bit ptr, root) :: vars) := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, spaceBound, limitBound⟩ := related
  obtain ⟨roots, absInv, rootWords⟩ := wordInv
  have absInv' : absMlInv conf ([value] ++ .refPtr bit ptr :: vars.map Prod.fst) refs
      (roots, heap, be, a, sp, sp1, gens) limit next := by simpa using absInv
  obtain ⟨p, rs, roots2, oldRoots, firstRoot, heap2, u, rootsEq, firstEq, lengthEq,
    _, oldLookup, oldLength, stored, absUpdated⟩ :=
    updateRefElementCore conf value [] (vars.map Prod.fst) bit ptr refs roots heap be a sp sp1 gens limit next index old
      ⟨by simpa using absInv', found, bound⟩
  cases rs with
  | nil => simp at firstEq
  | cons first rest =>
    simp only [List.head?_cons, Option.some.injEq] at firstEq
    subst first
    have restNil : rest = [] := by
      cases rest with
      | nil => rfl
      | cons head tail => simp at lengthEq
    subst rest
    simp only [List.nil_append, List.cons_append] at rootsEq
    rw [rootsEq] at rootWords
    cases rootWords with
    | cons valueAddr remaining =>
      cases remaining with
      | cons ptrAddr tail =>
        have wordEq : wordAddr conf firstRoot = word := valueAddr
        have rootEq : root = .word (getAddr conf p u) := by simpa [wordAddr] using ptrAddr.symm
        obtain ⟨pre, post, heapEq, pEq⟩ := heapLookup_split heap p _ oldLookup
        subst heap
        subst p
        have canonical := heapStore_refBlock pre post (oldRoots.set index firstRoot) oldRoots (by simp)
        have heapEq2 : heap2 = pre ++ refBlock (oldRoots.set index firstRoot) :: post := by
          have eq := stored.symm.trans canonical
          exact congrArg Prod.fst eq
        subst heap2
        have indexBound : index < oldRoots.length := by omega
        have heapMem' : heapInMemoryStore (pre ++ [refBlock oldRoots] ++ post)
            a sp sp1 gens conf store memory domain limit := by simpa [List.append_assoc] using heapMem
        obtain ⟨curr, currStore, domainEq, memoryNew⟩ :=
          heapInMemoryStore_refStore conf oldRoots firstRoot pre post a sp sp1 gens store memory domain limit index indexBound heapMem'
        have address := (getRealAddr_getAddr conf store _ (heapLength pre) _ curr u
          ⟨heapMem'.1, by simpa [List.append_assoc] using oldLookup, currStore, good⟩).2
        refine ⟨getAddr conf (heapLength pre) u,
          curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre), rootEq, ?_, domainEq, ?_⟩
        · simpa [BitVec.mul_comm] using address
        · refine ⟨pre ++ [refBlock (oldRoots.set index firstRoot)] ++ post, limit, a, sp, sp1, gens,
            ?_, ?_, spaceBound, limitBound⟩
          · simpa [wordEq] using memoryNew
          · refine ⟨firstRoot :: .pointer (heapLength pre) u :: roots2, ?_, ?_⟩
            · simpa [rootsEq, List.append_assoc] using absUpdated
            · exact .cons valueAddr (.cons ptrAddr tail)

/-- A word write to the selected array element preserves the full memory
relation with the corresponding source reference update. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Update'"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_updateRef {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (value : Flapjack.Compiler.Backend.DataSem.Value) (word : WordLocW width)
    (bit : Bool) (ptr : Nat) (root : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (old : List Flapjack.Compiler.Backend.DataSem.Value) (index : Nat)
    (valid : memoryRel conf be next refs space store memory domain ((value, word) :: (.refPtr bit ptr, root) :: vars) ∧
      sptLookup ptr refs = some (.valueArray old) ∧ goodDimindex width ∧ index < old.length) :
    ∃ ptrWord addr, root = .word ptrWord ∧ getRealAddr conf store ptrWord = some addr ∧
      domain (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width index) = true ∧
      memoryRel conf be next (sptInsert ptr (.valueArray (old.set index value)) refs) space store
        (fun key => if key = addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width index
          then word else memory key) domain ((value, word) :: (.refPtr bit ptr, root) :: vars) := by
  obtain ⟨related, found, good, bound⟩ := valid
  obtain ⟨ptrWord, addr, rootEq, real, inDomain, updated⟩ :=
    memoryRel_refStore conf be next refs space store memory domain value word bit ptr root vars old index found bound good related
  exact ⟨ptrWord, addr, rootEq, real, by simpa [BitVec.mul_comm] using inDomain,
    by simpa [BitVec.mul_comm] using updated⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
