import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorRoots

/-! Filtering code locations from a successful collector run. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.WordGcFunctions

open Classical in
/-- A successful run with valid locations cannot fail when those locations
are filtered from the input. -/
theorem wordGcFun_filter_ne_none {width : Nat} [NeZero width] (conf : Config)
    (roots moved : List (WordLocW width)) (memory memory' : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (store' : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (run : wordGcFun conf (roots, memory, domain, store) = some (moved, memory', store'))
    (valid : roots.all locOk = true) :
    wordGcFun conf (roots.filter wordSemIsWordLoc, memory, domain, store) ≠ none := by
  have assum := wordGcFun_assum_of_success conf roots moved memory memory' domain store store' run
  have globalWord : wordSemIsWordLoc (holFapply store .globals) = true := assum.2.2.2.2.2.2.2.1
  intro noRun
  cases global : holFapply store .globals with
  | loc a b => simp [global, wordSemIsWordLoc] at globalWord
  | word g =>
    have allValid : ((.word g : WordLocW width) :: roots).all locOk = true := by simp [locOk, valid]
    cases kind : conf.gcKind with
    | none => simp [wordGcFun, kind, assum] at noRun
    | simple =>
      have full := wordFullGc_filter_eq conf (.word g :: roots) allValid
        (wordSemTheWord (holFapply store .otherHeap)) (wordSemTheWord (holFapply store .currHeap)) memory domain
      simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte] at full
      simp only [wordGcFun, kind, global] at run noRun
      rw [full] at run
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
          simp only [output, locMerge, List.tail_cons, holHd] at run noRun
          split at run <;> simp_all
    | generational genSizes =>
      simp only [wordGcFun, kind, global, assum, not_true_eq_false, ↓reduceIte] at run noRun
      by_cases canPartial : wordGenGcCanDoPartial genSizes store
      · simp only [canPartial, ↓reduceIte] at run noRun
        have full := wordGenGcPartialFull_filter_eq conf (.word g :: roots) allValid
          (wordSemTheWord (holFapply store .currHeap)) (wordSemTheWord (holFapply store .otherHeap))
          (wordSemTheWord (holFapply store .heapLength)) memory domain
          (wordSemTheWord (holFapply store .genStart))
          (wordSemTheWord (holFapply store .endOfHeap) - wordSemTheWord (holFapply store .currHeap))
        simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte] at full
        rw [full] at run
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
            simp only [output, locMerge, List.tail_cons, holHd] at run noRun
            split at run <;> simp_all
      · simp only [canPartial, ↓reduceIte] at run noRun
        have full := wordGenGc_filter_eq conf (.word g :: roots) allValid
          (wordSemTheWord (holFapply store .currHeap)) (wordSemTheWord (holFapply store .otherHeap))
          (wordSemTheWord (holFapply store .heapLength)) memory domain
        simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte] at full
        rw [full] at run
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
            simp only [output, locMerge, List.tail_cons, holHd] at run noRun
            split at run <;> simp_all

private theorem filter_locMerge_of_rootRel {width : Nat} [NeZero width]
    (roots moved : List (WordLocW width))
    (related : ListRel gcRootRel (roots.filter wordSemIsWordLoc) moved) :
    (locMerge roots moved).filter wordSemIsWordLoc = moved := by
  induction roots generalizing moved with
  | nil =>
    cases related
    rfl
  | cons root roots ih =>
    cases root with
    | loc a b =>
      simp only [List.filter_cons, wordSemIsWordLoc, Bool.false_eq_true, ↓reduceIte] at related
      simp only [locMerge, List.filter_cons, wordSemIsWordLoc, Bool.false_eq_true, ↓reduceIte]
      exact ih moved related
    | word w =>
      simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte] at related
      cases related with
      | cons head tail =>
        rename_i result results
        cases result with
        | loc a b => simp [gcRootRel, wordSemIsWordLoc] at head
        | word v =>
          simp only [locMerge, List.filter_cons, wordSemIsWordLoc, ↓reduceIte]
          rw [ih results tail]

open Classical in
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_fun_IMP_FILTER"
  (fmap_as_finite_support_relation := [store, store']) (words_as_type_indexed_bitvec)]
theorem wordGcFun_imp_filter {width : Nat} [NeZero width] (conf : Config)
    (roots moved : List (WordLocW width)) (memory memory' : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (store' : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (run : wordGcFun conf (roots, memory, domain, store) = some (moved, memory', store'))
    (valid : roots.all locOk = true) :
    wordGcFun conf (roots.filter wordSemIsWordLoc, memory, domain, store) =
      some (moved.filter wordSemIsWordLoc, memory', store') := by
  have existsRun := wordGcFun_filter_ne_none conf roots moved memory memory' domain store store' run valid
  obtain ⟨⟨filteredRoots, filteredMemory, filteredStore⟩, filteredRun⟩ := Option.ne_none_iff_exists'.mp existsRun
  have merged := wordGcFun_locMerge conf roots filteredRoots memory filteredMemory domain store filteredStore filteredRun valid
  rw [run] at merged
  simp only [Option.some.injEq, Prod.mk.injEq] at merged
  obtain ⟨rootsEq, rfl, rfl⟩ := merged
  have related := word_gc_IMP_EVERY2 filteredRun
  rw [rootsEq, filter_locMerge_of_rootRel roots filteredRoots related]
  exact filteredRun

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
