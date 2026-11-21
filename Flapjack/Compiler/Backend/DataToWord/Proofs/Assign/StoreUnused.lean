module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.UnusedWrite
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreConsts
@[expose] public section

/-! Stores into reserved allocation space preserve the memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A successful bounded store at NextFree retains the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "memory_rel_store_list_to_unused"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_storeListToUnused {width : Nat} [NeZero width] (conf : Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory result : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (DataSem.Value × WordLocW width)) (free : BitVec width) (ws : List (WordLocW width))
    (rel : memoryRel conf be ts refs space store memory domain vars)
    (run : storeList free ws memory domain = some result)
    (freeEq : store.lookup .nextFree = some (.word free)) (bound : ws.length ≤ space) :
    memoryRel conf be ts refs space store result domain vars := by
  induction ws using List.reverseRecOn generalizing memory result with
  | nil =>
    simp [storeList] at run
    subst result
    exact rel
  | @append_singleton ws word ih =>
    rw [storeList_append] at run
    cases hp : storeList free ws memory domain with
    | none => simp [hp] at run
    | some intermediate =>
      simp only [hp] at run
      have oldRel := ih memory intermediate rel hp (by simp at bound; omega)
      obtain ⟨free2, lookup, writable⟩ := memoryRel_write conf be ts refs space store intermediate domain vars word oldRel
      have same : free2 = free := by rw [freeEq] at lookup; exact (WordLocW.word.inj (Option.some.inj lookup)).symm
      subst free2
      have writableAt := writable ws.length (by simp at bound; omega)
      dsimp only at writableAt
      have addrEq : wordSemBytesInWord = (StackRemove.bytesInWord width : BitVec width) := rfl
      rw [addrEq] at run
      simp only [storeList, writableAt.1, ↓reduceIte] at run
      cases run
      exact writableAt.2
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
