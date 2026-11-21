module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit

@[expose] public section

/-! Generational `abs_ml_inv` lemmas of `data_to_word_gcProofScript.sml`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Exact HOL `abs_ml_inv_ADD` (`data_to_word_gcProofScript.sml:4321-4328`, a
`[local]` theorem); the HOL free variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "abs_ml_inv_ADD"
  (words_as_type_indexed_bitvec)]
theorem abs_ml_inv_ADD {width : Nat} [NeZero width] {c : Flapjack.Compiler.Backend.DataToWord.Config}
    {xs : List Flapjack.Compiler.Backend.DataSem.Value}
    {refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)}
    {ys : List (HeapAddress (WordLocW width))} {heap2 : ValueHeap width} {be : Bool}
    {a2 k2 k3 : Nat} {gens2 : GcCombined.GenState} {limit ts : Nat} {l : List Nat} :
    absMlInv c xs refs (ys, heap2, be, a2, k2 + k3, 0, gens2) limit ts ∧
        c.gcKind = .generational l →
      absMlInv c xs refs (ys, heap2, be, a2, k2, k3, gens2) limit ts := by
  rintro ⟨h, hk⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, ?_, by simpa using h4, h5⟩
  simp only [gcKindInv, hk] at h3 ⊢
  rw [show a2 + k2 + k3 = a2 + (k2 + k3) + 0 by omega]
  exact h3

/-- A lookup at the end of a heap prefix starts the suffix. Flapjack proof
infrastructure; no HOL counterpart. -/
private theorem heapLookup_append_length {α β : Type} (f s : List (HeapElement α β)) :
    heapLookup (heapLength f) (f ++ s) = heapLookup 0 s := by
  induction f with
  | nil => simp [heapLength]
  | cons x xs ih =>
    have hx : 0 < elLength x := by cases x <;> simp [elLength]
    simp only [heapLength, List.map_cons, List.sum_cons, List.cons_append, heapLookup] at ih ⊢
    rw [if_neg (by omega), if_neg (by omega), show elLength x + (xs.map elLength).sum - elLength x =
      (xs.map elLength).sum by omega]
    exact ih

open Classical in
/-- Exact HOL `abs_ml_inv_GenState_IMP_heap_length_FILTER`
(`data_to_word_gcProofScript.sml:3929-3968`); HOL `FILTER isDataElement` is
`List.filter` of the decided predicate and `EVERY` is a bounded universal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "abs_ml_inv_GenState_IMP_heap_length_FILTER"
  (words_as_type_indexed_bitvec)]
theorem abs_ml_inv_GenState_IMP_heap_length_FILTER {width : Nat} [NeZero width] {c : Flapjack.Compiler.Backend.DataToWord.Config}
    {stack : List Flapjack.Compiler.Backend.DataSem.Value}
    {refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)}
    {xs : List (HeapAddress (WordLocW width))} {heap : ValueHeap width} {be : Bool}
    {a sp sp1 n t : Nat} {ts : List Nat} {tss y : Nat} {ys : List Nat}
    {h1 h2 : ValueHeap width} :
    absMlInv c stack refs (xs, heap, be, a, sp, sp1, .genState n (t :: ts)) (heapLength heap) tss ∧
        c.gcKind = .generational (y :: ys) ∧ heapSplit (a + sp + sp1) heap = some (h1, h2) →
      (∀ e ∈ h2, isDataElement e) ∧
        heapLength (heap.filter (fun e => decide (isDataElement e))) = a + heapLength h2 := by
  rintro ⟨⟨_, _, kind, unused, _⟩, hk, split⟩
  simp only [gcKindInv, hk] at kind
  obtain ⟨_, first, second, split', _, refsSecond⟩ := kind
  rw [split] at split'
  cases split'
  have dataH2 : ∀ e ∈ h2, isDataElement e := by
    intro e he
    have := refsSecond e he
    cases e with
    | dataElement xs len payload => exact ⟨xs, len, payload, rfl⟩
    | unused len => exact this.elim
    | forwardPointer p v len => exact this.elim
  refine ⟨dataH2, ?_⟩
  obtain ⟨hlook, _, f, s, splitA, dataF⟩ := unused
  obtain ⟨hfLen, _, hfs⟩ := heapSplit_heapLength heap f s a splitA
  obtain ⟨hh1Len, _, hh12⟩ := heapSplit_heapLength heap h1 h2 (a + sp + sp1) split
  have filterId : ∀ l : ValueHeap width, (∀ e ∈ l, isDataElement e) →
      l.filter (fun e => decide (isDataElement e)) = l := fun l hl =>
    List.filter_eq_self.mpr (fun e he => by simpa using hl e he)
  by_cases hz : sp + sp1 = 0
  · have : a + sp + sp1 = a := by omega
    rw [this] at split
    rw [splitA] at split
    cases split
    rw [← hfs, List.filter_append, filterId _ dataF, filterId _ dataH2, heapLength_append, hfLen]
  · have look := hlook hz
    rw [← hfs, ← hfLen, heapLookup_append_length] at look
    cases s with
    | nil => simp [heapLookup] at look
    | cons u rest =>
      simp only [heapLookup, if_true, Option.some.injEq] at look
      subst look
      have hsplit : heapSplit (heapLength (f ++ [HeapElement.unused (sp + sp1 - 1)]))
          ((f ++ [HeapElement.unused (sp + sp1 - 1)]) ++ rest) =
            some (f ++ [HeapElement.unused (sp + sp1 - 1)], rest) := heapSplit_append _ _
      have hlen : heapLength (f ++ [HeapElement.unused (sp + sp1 - 1)] : ValueHeap width) =
          a + sp + sp1 := by
        rw [heapLength_append, hfLen]
        simp [heapLength, elLength]
        omega
      rw [hlen, List.append_assoc, List.singleton_append, hfs, split] at hsplit
      simp only [Option.some.injEq, Prod.mk.injEq] at hsplit
      obtain ⟨_, rfl⟩ := hsplit
      have notData : ¬ (decide (isDataElement (HeapElement.unused (sp + sp1 - 1) :
          HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) = true) := by
        simp [isDataElement]
      rw [← hfs, List.filter_append, filterId _ dataF, List.filter_cons, if_neg notData,
        filterId _ dataH2, heapLength_append, hfLen]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
