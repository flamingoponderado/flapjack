module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConcreteAlloc
@[expose] public section

/-! Writes to unused allocation space preserve the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- Replacing a word inside an existentially represented list preserves the
separated list and arbitrary frame, and the selected address lies in the domain. -/
private theorem wordListExists_write {width : Nat} [NeZero width] (base : BitVec width)
    (len idx : Nat) (value : WordLocW width) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (bound : idx < len)
    (sep : SetSep.star (Misc.wordListExists base len) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    domain (base + BitVec.ofNat width idx * StackRemove.bytesInWord width) = true ∧
    SetSep.star (Misc.wordListExists base len) frame
      (SetSep.fun2Set ((fun key => if key = base + BitVec.ofNat width idx * StackRemove.bytesInWord width
        then value else memory key), fun addr => domain addr = true)) := by
  obtain ⟨left, right, part, ⟨xs, hx⟩, frameRight⟩ := sep
  obtain ⟨xsLeft, length⟩ := (StackRemove.WordListExists.starCond _ _ _).mp hx
  have inRange : idx < xs.length := by omega
  have sepList : SetSep.star (Misc.wordList base xs) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true)) :=
    ⟨left, right, part, xsLeft, frameRight⟩
  have member := wordList_indexMember xs idx inRange base left xsLeft
  have memGraph : SetSep.fun2Set (memory, fun addr => domain addr = true)
      (base + BitVec.ofNat width idx * StackRemove.bytesInWord width, xs[idx]) := by
    rw [← part.1]
    exact Or.inl member
  have inDomain := ((SetSep.fun2SetThm memory (fun addr => domain addr = true) _ _).mp memGraph).2
  have changed := wordList_write base xs idx value memory (fun addr => domain addr = true) frame inRange sepList
  obtain ⟨left2, right2, part2, xsLeft2, frameRight2⟩ := changed
  refine ⟨inDomain, left2, right2, part2, ?_, frameRight2⟩
  exact ⟨xs.set idx value, (StackRemove.WordListExists.starCond _ _ _).mpr ⟨xsLeft2, by simpa using length⟩⟩

/-- Isolate an unused heap segment, preserving both heaps and the frame. -/
private theorem heapUnused_write {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (a freeCount idx : Nat) (curr : BitVec width)
    (value : WordLocW width) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (bound : idx < freeCount)
    (found : heapLookup a heap = some (.unused (freeCount - 1)))
    (sep : SetSep.star (wordHeap curr heap conf) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width a
    let address := base + BitVec.ofNat width idx * StackRemove.bytesInWord width
    domain address = true ∧
    SetSep.star (wordHeap curr heap conf) frame
      (SetSep.fun2Set ((fun key => if key = address then value else memory key),
        fun addr => domain addr = true)) := by
  obtain ⟨pre, post, heapEq, indexEq⟩ := heapLookup_split heap a _ found
  subst heap
  subst a
  dsimp only
  rw [wordHeapAppend] at sep ⊢
  simp only [wordHeap, wordEl] at sep ⊢
  repeat rw [← SetSep.starAssoc] at sep ⊢
  rw [star_swap_first] at sep ⊢
  have h := wordListExists_write
    (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre))
    (freeCount - 1 + 1) idx value memory domain _ (by omega) sep
  exact h


/-- Every reserved allocation word can be overwritten without changing the
memory relation, and the corresponding concrete address is in the domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_write"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_write {width : Nat} [NeZero width] (conf : Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (DataSem.Value × WordLocW width)) (value : WordLocW width)
    (rel : memoryRel conf be ts refs space store memory domain vars) :
    ∃ free : BitVec width, store.lookup .nextFree = some (.word free) ∧
      ∀ n, n < space →
        let addr := free + StackRemove.bytesInWord width * BitVec.ofNat width n
        domain addr = true ∧ memoryRel conf be ts refs space store
          (fun key => if key = addr then value else memory key) domain vars := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, sizeBound, spaceBound⟩ := rel
  obtain ⟨heapBound, byteBound, shiftBound, lenPos, lenBound, shiftWidth, globals, curr, other,
    currAligned, otherAligned, currLookup, otherLookup, freeLookup, triggerLookup, endLookup,
    heapLenLookup, globInv, genInv, heapSep⟩ := heapMem
  have unused : unusedSpaceInv a (sp + sp1) heap := by
    obtain ⟨roots, inv, addresses⟩ := wordInv
    exact inv.2.2.2.1
  refine ⟨curr + StackRemove.bytesInWord width * BitVec.ofNat width a, freeLookup, ?_⟩
  intro n nBound
  have positive : sp + sp1 ≠ 0 := by omega
  have found := unused.1 positive
  have h := heapUnused_write conf heap a (sp + sp1) n curr value memory domain
    (wordHeap other (heapExpand limit) conf) (by omega) found heapSep
  dsimp only at h ⊢
  have addressEq : curr + StackRemove.bytesInWord width * BitVec.ofNat width a +
      BitVec.ofNat width n * StackRemove.bytesInWord width =
      curr + StackRemove.bytesInWord width * BitVec.ofNat width a +
        StackRemove.bytesInWord width * BitVec.ofNat width n := by ac_rfl
  rw [addressEq] at h
  refine ⟨h.1, heap, limit, a, sp, sp1, gens, ?_, wordInv, sizeBound, spaceBound⟩
  exact ⟨heapBound, byteBound, shiftBound, lenPos, lenBound, shiftWidth, globals, curr, other,
    currAligned, otherAligned, currLookup, otherLookup, freeLookup, triggerLookup, endLookup,
    heapLenLookup, globInv, genInv, h.2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
