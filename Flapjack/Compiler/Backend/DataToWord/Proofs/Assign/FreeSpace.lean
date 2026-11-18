module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapExpand
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store

@[expose] public section

/-! Free-space extraction for the assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The unused region implied by the complete memory relation is available
at the machine's NextFree address, with the rest of memory as a frame. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "memory_rel_IMP_free_space"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_freeSpace {width : Nat} [NeZero width]
    (conf : Config) (be : Bool) (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (DataSem.Value × WordLocW width))
    (related : memoryRel conf be next refs space store memory domain vars) :
    ∃ nfree curr : BitVec width, ∃ other : ((BitVec width × WordLocW width) → Prop) → Prop,
      store.lookup .nextFree = some (.word nfree) ∧ store.lookup .currHeap = some (.word curr) ∧
      SetSep.star (Misc.wordListExists nfree space) other
        (SetSep.fun2Set (memory, fun addr => domain addr = true)) := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, spaceBound⟩ := related
  obtain ⟨roots, abstract, _⟩ := wordInv
  have unused := abstract.2.2.2.1
  rcases heapMem with ⟨_, _, _, _, _, _, _, curr, alternate, _, _, currLookup, _, nextLookup, _, _, _, _, _, separated⟩
  by_cases zero : space = 0
  · subst space
    refine ⟨curr + StackRemove.bytesInWord width * BitVec.ofNat width a, curr,
      SetSep.star (wordHeap curr heap conf) (wordHeap alternate (heapExpand limit) conf), nextLookup, currLookup, ?_⟩
    rw [(StackRemove.WordListExists.wordListExistsThm (β := WordLocW width) _ 0).1,
      StackRemove.StackHeap.starEmptyLeft]
    exact separated
  · have positive : sp + sp1 ≠ 0 := by omega
    have lookup := unused.1 positive
    obtain ⟨before, after, heapEq, offsetEq⟩ := heapLookup_split heap a _ lookup
    subst heap
    subst a
    rw [wordHeapAppend] at separated
    simp only [wordHeap, wordEl] at separated
    have splitLength : sp + sp1 - 1 + 1 = space + ((sp + sp1) - space) := by omega
    rw [splitLength, StackRemove.Proofs.WordListMemory.wordListExistsAdd] at separated
    simp only [← SetSep.starAssoc] at separated
    rw [SetSep.starAssoc,
      SetSep.starComm (wordHeap curr before conf)
        (Misc.wordListExists (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before)) space),
      ← SetSep.starAssoc] at separated
    exact ⟨curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before), curr, _,
      nextLookup, currLookup, separated⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
