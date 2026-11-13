module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveRoots

@[expose] public section

/-! Root correspondence for complete collector traversals. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.WordGcFunctions

/-- Simple collection changes only the word roots; its subsequent heap scan
is the same as in the word-only execution. -/
theorem wordFullGc_filter_eq {width : Nat} [NeZero width] (conf : Config)
    (roots : List (WordLocW width)) (valid : roots.all locOk = true)
    (new old : BitVec width) (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) :
    wordFullGc conf (roots, new, old, memory, domain) =
      let (moved, i, pa, memory', ok) :=
        wordFullGc conf (roots.filter wordSemIsWordLoc, new, old, memory, domain)
      (locMerge roots moved, i, pa, memory', ok) := by
  simp only [wordFullGc, wordGcMoveRoots_filter_eq conf roots valid 0 new old memory domain]

/-- Partial generational collection preserves code locations while executing
the same reference and data scans on the moved words. -/
theorem wordGenGcPartial_filter_eq {width : Nat} [NeZero width] (conf : Config)
    (roots : List (WordLocW width)) (valid : roots.all locOk = true)
    (curr new len : BitVec width) (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (gs rs : BitVec width) :
    wordGenGcPartial conf (roots, curr, new, len, memory, domain, gs, rs) =
      let (moved, i, pa, memory', ok) :=
        wordGenGcPartial conf (roots.filter wordSemIsWordLoc, curr, new, len, memory, domain, gs, rs)
      (locMerge roots moved, i, pa, memory', ok) := by
  simp only [wordGenGcPartial,
    wordGenGcPartialMoveRoots_filter_eq conf roots valid (gs >>> wordShiftAmount width) new curr memory domain gs rs]

/-- Partial collection followed by copying has the same root correspondence. -/
theorem wordGenGcPartialFull_filter_eq {width : Nat} [NeZero width] (conf : Config)
    (roots : List (WordLocW width)) (valid : roots.all locOk = true)
    (curr new len : BitVec width) (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (gs rs : BitVec width) :
    wordGenGcPartialFull conf (roots, curr, new, len, memory, domain, gs, rs) =
      let (moved, i, pa, memory', ok) :=
        wordGenGcPartialFull conf (roots.filter wordSemIsWordLoc, curr, new, len, memory, domain, gs, rs)
      (locMerge roots moved, i, pa, memory', ok) := by
  simp only [wordGenGcPartialFull, wordGenGcPartial_filter_eq conf roots valid curr new len memory domain gs rs]

/-- Full generational collection preserves code locations and agrees on both
heap areas with the word-only execution. -/
theorem wordGenGc_filter_eq {width : Nat} [NeZero width] (conf : Config)
    (roots : List (WordLocW width)) (valid : roots.all locOk = true)
    (curr new len : BitVec width) (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) :
    wordGenGc conf (roots, curr, new, len, memory, domain) =
      let (moved, i, pa, ib, pb, memory', ok) :=
        wordGenGc conf (roots.filter wordSemIsWordLoc, curr, new, len, memory, domain)
      (locMerge roots moved, i, pa, ib, pb, memory', ok) := by
  simp only [wordGenGc, wordGenGcMoveRoots_filter_eq conf roots valid 0 new
    (len >>> wordShiftAmount width) (new + len) curr memory domain]

open Classical in
/-- A successful collector run establishes the store assumptions required
by its selected implementation. -/
theorem wordGcFun_assum_of_success {width : Nat} [NeZero width] (conf : Config)
    (roots moved : List (WordLocW width)) (memory memory' : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (store store' : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (run : wordGcFun conf (roots, memory, domain, store) = some (moved, memory', store')) :
    wordGcFunAssum conf store := by
  simp only [wordGcFun] at run
  cases conf.gcKind <;> split at run <;> simp_all

open Classical in
/-- The collector's store-level result is independent of code-location roots,
which are restored after collecting the filtered words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_fun_loc_merge"
  (fmap_as_finite_support_relation := [store, store']) (words_as_type_indexed_bitvec)]
theorem wordGcFun_locMerge {width : Nat} [NeZero width] (conf : Config)
    (roots moved : List (WordLocW width)) (memory memory' : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (store' : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (run : wordGcFun conf (roots.filter wordSemIsWordLoc, memory, domain, store) = some (moved, memory', store'))
    (valid : roots.all locOk = true) :
    wordGcFun conf (roots, memory, domain, store) = some (locMerge roots moved, memory', store') := by
  have assum := wordGcFun_assum_of_success conf _ _ memory memory' domain store store' run
  have globalWord : wordSemIsWordLoc (holFapply store .globals) = true := assum.2.2.2.2.2.2.2.1
  cases global : holFapply store .globals with
  | loc a b => simp [global, wordSemIsWordLoc] at globalWord
  | word g =>
    have allValid : ((.word g : WordLocW width) :: roots).all locOk = true := by simp [locOk, valid]
    cases kind : conf.gcKind with
    | none =>
      simp only [wordGcFun, kind, ite_eq_left assum, Option.some.injEq, Prod.mk.injEq] at run ⊢
      obtain ⟨rfl, rfl, rfl⟩ := run
      simp [locMerge_filter_isWord]
    | simple =>
      have full := wordFullGc_filter_eq conf (.word g :: roots) allValid
        (wordSemTheWord (holFapply store .otherHeap)) (wordSemTheWord (holFapply store .currHeap)) memory domain
      simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte] at full
      simp only [wordGcFun, kind, global] at run ⊢
      rw [full]
      have nonempty : (wordFullGc conf (.word g :: roots.filter wordSemIsWordLoc,
          wordSemTheWord (holFapply store .otherHeap), wordSemTheWord (holFapply store .currHeap), memory, domain)).1 ≠ [] := by
        rw [wordFullGc_fst]
        have rel := wordGcMoveRoots_rootRel conf (.word g :: roots.filter wordSemIsWordLoc) 0
          (wordSemTheWord (holFapply store .otherHeap)) (wordSemTheWord (holFapply store .currHeap)) memory domain
        intro empty
        rw [empty] at rel
        cases rel
      cases output : wordFullGc conf (.word g :: roots.filter wordSemIsWordLoc,
          wordSemTheWord (holFapply store .otherHeap), wordSemTheWord (holFapply store .currHeap), memory, domain) with
      | mk result rest =>
        rcases rest with ⟨i, pa, mem, ok⟩
        cases result with
        | nil => simp [output] at nonempty
        | cons head tail =>
          simp only [output, locMerge, List.tail_cons] at run ⊢
          simp only [holHd] at run ⊢
          split at run <;> simp_all
    | generational genSizes =>
      simp only [wordGcFun, kind, global, assum, not_true_eq_false, ↓reduceIte] at run ⊢
      by_cases canPartial : wordGenGcCanDoPartial genSizes store
      · simp only [canPartial, ↓reduceIte] at run ⊢
        have full := wordGenGcPartialFull_filter_eq conf (.word g :: roots) allValid
          (wordSemTheWord (holFapply store .currHeap)) (wordSemTheWord (holFapply store .otherHeap))
          (wordSemTheWord (holFapply store .heapLength)) memory domain
          (wordSemTheWord (holFapply store .genStart))
          (wordSemTheWord (holFapply store .endOfHeap) - wordSemTheWord (holFapply store .currHeap))
        simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte] at full
        rw [full]
        have nonempty : (wordGenGcPartialFull conf (.word g :: roots.filter wordSemIsWordLoc,
            wordSemTheWord (holFapply store .currHeap), wordSemTheWord (holFapply store .otherHeap),
            wordSemTheWord (holFapply store .heapLength), memory, domain,
            wordSemTheWord (holFapply store .genStart),
            wordSemTheWord (holFapply store .endOfHeap) - wordSemTheWord (holFapply store .currHeap))).1 ≠ [] := by
          rw [wordGenGcPartialFull_fst]
          have rel := wordGenGcPartialMoveRoots_rootRel conf (.word g :: roots.filter wordSemIsWordLoc)
            (wordSemTheWord (holFapply store .genStart) >>> wordShiftAmount width)
            (wordSemTheWord (holFapply store .otherHeap)) (wordSemTheWord (holFapply store .currHeap))
            memory domain (wordSemTheWord (holFapply store .genStart))
            (wordSemTheWord (holFapply store .endOfHeap) - wordSemTheWord (holFapply store .currHeap))
          intro empty
          rw [empty] at rel
          cases rel
        cases output : wordGenGcPartialFull conf (.word g :: roots.filter wordSemIsWordLoc,
            wordSemTheWord (holFapply store .currHeap), wordSemTheWord (holFapply store .otherHeap),
            wordSemTheWord (holFapply store .heapLength), memory, domain,
            wordSemTheWord (holFapply store .genStart),
            wordSemTheWord (holFapply store .endOfHeap) - wordSemTheWord (holFapply store .currHeap)) with
        | mk result rest =>
          rcases rest with ⟨i, pa, mem, ok⟩
          cases result with
          | nil => simp [output] at nonempty
          | cons head tail =>
            simp only [output, locMerge, List.tail_cons, holHd] at run ⊢
            split at run <;> simp_all
      · simp only [canPartial, ↓reduceIte] at run ⊢
        have full := wordGenGc_filter_eq conf (.word g :: roots) allValid
          (wordSemTheWord (holFapply store .currHeap)) (wordSemTheWord (holFapply store .otherHeap))
          (wordSemTheWord (holFapply store .heapLength)) memory domain
        simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte] at full
        rw [full]
        have nonempty : (wordGenGc conf (.word g :: roots.filter wordSemIsWordLoc,
            wordSemTheWord (holFapply store .currHeap), wordSemTheWord (holFapply store .otherHeap),
            wordSemTheWord (holFapply store .heapLength), memory, domain)).1 ≠ [] := by
          rw [wordGenGc_fst]
          have rel := wordGenGcMoveRoots_rootRel conf (.word g :: roots.filter wordSemIsWordLoc) 0
            (wordSemTheWord (holFapply store .otherHeap))
            (wordSemTheWord (holFapply store .heapLength) >>> wordShiftAmount width)
            (wordSemTheWord (holFapply store .otherHeap) + wordSemTheWord (holFapply store .heapLength))
            (wordSemTheWord (holFapply store .currHeap)) memory domain
          intro empty
          rw [empty] at rel
          cases rel
        cases output : wordGenGc conf (.word g :: roots.filter wordSemIsWordLoc,
            wordSemTheWord (holFapply store .currHeap), wordSemTheWord (holFapply store .otherHeap),
            wordSemTheWord (holFapply store .heapLength), memory, domain) with
        | mk result rest =>
          rcases rest with ⟨i, pa, ib, pb, mem, ok⟩
          cases result with
          | nil => simp [output] at nonempty
          | cons head tail =>
            simp only [output, locMerge, List.tail_cons, holHd] at run ⊢
            split at run <;> simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
