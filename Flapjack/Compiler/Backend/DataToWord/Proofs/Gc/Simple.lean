module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FullStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation

@[expose] public section

/-! Correctness of the Simple store-level collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.CopyingGc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private theorem forallMap {α β : Type} (f : α → β) (xs : List α) (ys : List β) :
    List.Forall₂ (fun x y => f x = y) xs ys ↔ ys = xs.map f := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih => cases ys <;> simp [List.forall₂_cons_left_iff, ih, and_comm]

/-- The Simple collector preserves the heap/store invariant and stack roots. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_fun_lemma_Simple"
  (fmap_as_finite_support_relation := [store, outStore]) (words_as_type_indexed_bitvec)]
theorem wordGcFun_lemma_simple {width : Nat} [NeZero width] (conf : Config)
    (value : DataSem.Value) (stack : List (DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref DataSem.Value)) (root : HeapAddress (WordLocW width))
    (roots roots2 : List (HeapAddress (WordLocW width)))
    (heap heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (be : Bool) (a sp sp1 limit ts : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (_abstractInv : absMlInv conf (value :: stack.map Prod.fst) refs
      (root :: roots, heap, be, a, sp, sp1, gens) limit ts)
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit)
    (global : wordAddr conf root = holFapply store .globals)
    (related : List.Forall₂ (fun v w => wordAddr conf v = w) roots (stack.map Prod.snd))
    (run : fullGc (root :: roots, heap, limit) = (roots2, heap2, heapLength heap2, true))
    (kind : conf.gcKind = .simple) :
    ∃ (stack1 : List (WordLocW width)) (outMemory : BitVec width → WordLocW width)
      (outStore : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (root1 : HeapAddress (WordLocW width)) (roots1 : List (HeapAddress (WordLocW width))),
      wordGcFun conf (stack.map Prod.snd, memory, domain, store) = some (stack1, outMemory, outStore) ∧
      heapInMemoryStore (heap2 ++ heapExpand (limit - heapLength heap2)) (heapLength heap2)
        (limit - heapLength heap2) 0 gens conf outStore outMemory domain limit ∧
      roots2 = root1 :: roots1 ∧ wordAddr conf root1 = holFapply outStore .globals ∧
      List.Forall₂ (fun v w => wordAddr conf v = w) roots1
        (((stack.map Prod.fst).zip stack1).map Prod.snd) ∧ stack1.length = stack.length := by
  have length := fullGc_imp_length (root :: roots) roots2 heap heap2 limit (heapLength heap2) run
  cases roots2 with
  | nil => simp at length
  | cons root1 roots1 =>
    have lookupExists := heapMem.2.2.2.2.2.2.1
    obtain ⟨w, lookup⟩ := lookupExists
    have globalLookup : store.lookup .globals = some (wordAddr conf root) := by
      rw [holFapply_of_lookup lookup] at global
      simpa [global] using lookup
    have rootsEq : stack.map Prod.snd = roots.map (wordAddr conf) := (forallMap _ _ _).mp related
    obtain ⟨outMemory, outStore, execution, invariant, newGlobal⟩ :=
      simpleGc_store_correct_word_global conf root root1 roots roots1 heap heap2 a sp sp1 limit gens
        store memory domain run kind globalLookup good heapMem
    have lengths : roots1.length = stack.length := by
      have rootLength := congrArg List.length rootsEq
      simp only [List.length_map] at rootLength
      simp only [List.length_cons] at length
      omega
    refine ⟨roots1.map (wordAddr conf), outMemory, outStore, root1, roots1, ?_, invariant, rfl, ?_, ?_, ?_⟩
    · simpa only [rootsEq] using execution
    · exact (holFapply_of_lookup newGlobal).symm
    · apply (forallMap _ _ _).mpr
      rw [List.map_snd_zip (by simp [lengths])]
    · simp [lengths]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
