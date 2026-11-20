module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshRefStack

@[expose] public section

/-! Fresh reference allocation in the abstract data-to-word memory invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Fresh value-array allocation preserves the complete abstract invariant.
The independent unused HOL witness type is modeled by `[Nonempty β]`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "new_ref_thm"
  (words_as_type_indexed_bitvec) (new_ref_existential_inhabitants := [β._p])]
theorem newRef {width : Nat} [NeZero width] {β : Type} [Nonempty β]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (values stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next ptr : Nat)
    (valid : absMlInv conf (values ++ stack) refs (roots, heap, be, a, sp, sp1, gens) limit next ∧
      ¬ sptDomain refs ptr ∧ values.length + 1 ≤ sp) :
    ∃ (_p : β) (rs roots2 : List (HeapAddress (WordLocW width))) (heap2 : ValueHeap width),
      roots = rs ++ roots2 ∧ rs.length = values.length ∧
      heapStoreUnused a (sp + sp1) (refBlock rs) heap = (heap2, true) ∧
      absMlInv conf (values ++ .refPtr true ptr :: stack) (sptInsert ptr (.valueArray values) refs)
        (rs ++ .pointer (a + sp + sp1 - (values.length + 1)) (.word 0) :: roots2,
          heap2, be, a, sp - (values.length + 1), sp1, gens) limit next := by
  obtain ⟨inv, fresh, fits⟩ := valid
  obtain ⟨rootsValid, heapValid, gcValid, unused, stackValid⟩ := inv
  have relatedLength : (values ++ stack).length = roots.length := by
    obtain ⟨_, _, _, _, _, _, _, _, _, related, _⟩ := stackValid
    exact related.length_eq
  let rs := roots.take values.length
  let roots2 := roots.drop values.length
  have rootsEq : roots = rs ++ roots2 := by simp [rs, roots2]
  have lengths : rs.length = values.length := by
    simp only [rs, List.length_take]
    have bound : values.length ≤ roots.length := by simp only [List.length_append] at relatedLength; omega
    exact Nat.min_eq_left bound
  have rootsBefore : rootsOk (rs ++ roots2) heap := by simpa [← rootsEq] using rootsValid
  obtain ⟨heap2, stored, unused2, found, oldNot, rel, rootsAfter, heapAfter, gcAfter⟩ :=
    heapStoreUnused_freshRef_valid conf a sp sp1 limit gens heap rs roots2 (.word 0) unused
      (by rw [lengths]; exact fits) rootsBefore heapValid gcValid
  have freshLookup : sptLookup ptr refs = none := by
    cases found : sptLookup ptr refs with
    | none => rfl
    | some value => exact False.elim (fresh ((sptDomain_iff_lookup refs ptr).mpr ⟨value, found⟩))
  have stackBefore : bcStackRefInv conf next (values ++ stack) refs (rs ++ roots2, heap, be) := by
    simpa [← rootsEq] using stackValid
  have stackAfter := bcStackRefInv_freshValueArray conf next values stack refs rs roots2 heap heap2 be ptr
    (a + sp + sp1 - (values.length + 1)) lengths.symm freshLookup
    (by simpa [lengths] using oldNot) rel (by simpa [lengths] using found) stackBefore
  refine ⟨Classical.choice (inferInstance : Nonempty β), rs, roots2, heap2, rootsEq, lengths, stored, ?_⟩
  exact ⟨by simpa [lengths] using rootsAfter, heapAfter, by simpa [lengths] using gcAfter,
    by simpa [lengths] using unused2, stackAfter⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
