import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateValueHeap
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateRefs

/-! Value-invariant preservation for value-array replacement. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A heap element is a reference block exactly when it is a `refBlock` for
some pointer list; the address and payload element types are independent. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isRefBlock_def"]
def isRefBlock {α β : Type} (cell : HeapElement α (HeapTag × List β)) : Prop :=
  ∃ pointers, cell = refBlock pointers

/-- Two heaps agree on every lookup whose result is not a reference block. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "RefBlock_inv_def"]
def refBlockInv {α β : Type} (heap heap2 : List (HeapElement α (HeapTag × List β))) : Prop :=
  (∀ n x, heapLookup n heap = some x ∧ ¬ isRefBlock x → heapLookup n heap2 = some x) ∧
  (∀ n x, heapLookup n heap2 = some x ∧ ¬ isRefBlock x → heapLookup n heap = some x)

/-- At a heap-prefix boundary, lookup returns the following reference block. -/
theorem heapLookup_refBlock_here {α β : Type} (pre post : List (HeapElement α (HeapTag × List β)))
    (pointers : List (HeapAddress α)) :
    heapLookup (heapLength pre) (pre ++ [refBlock pointers] ++ post) = some (refBlock pointers) := by
  induction pre with
  | nil => simp [heapLength, heapLookup]
  | cons head tail ih =>
    have positive : 0 < elLength head := by cases head <;> simp [elLength]
    change heapLookup (elLength head + heapLength tail) (head :: (tail ++ [refBlock pointers] ++ post)) = _
    simp only [heapLookup, show ¬ elLength head + heapLength tail = 0 by omega, ↓reduceIte,
      show ¬ elLength head + heapLength tail < elLength head by omega]
    simpa using ih

/-- Replacing an equally sized reference block preserves every non-reference
heap lookup in both directions. -/
theorem refBlockInv_replace {α β : Type} (pre post : List (HeapElement α (HeapTag × List β)))
    (before after : List (HeapAddress α)) (sameLength : before.length = after.length) :
    refBlockInv (pre ++ [refBlock before] ++ post) (pre ++ [refBlock after] ++ post) := by
  have size : elLength (refBlock (β := β) before) = elLength (refBlock (β := β) after) := by
    simp [refBlock, elLength, sameLength]
  constructor <;> intro n x conditions
  · by_cases here : n = heapLength pre
    · subst n
      have cell := (heapLookup_refBlock_here pre post before).symm.trans conditions.1
      have same : refBlock (β := β) before = x := Option.some.inj cell
      exact (conditions.2 ⟨before, same.symm⟩).elim
    · rw [← heapLookup_replace_ne pre post _ _ size n here]
      exact conditions.1
  · by_cases here : n = heapLength pre
    · subst n
      have cell := (heapLookup_refBlock_here pre post after).symm.trans conditions.1
      have same : refBlock (β := β) after = x := Option.some.inj cell
      exact (conditions.2 ⟨after, same.symm⟩).elim
    · rw [heapLookup_replace_ne pre post _ _ size n here]
      exact conditions.1

/-- The clocked value invariant survives any heap transformation that only
changes reference blocks. This is proof infrastructure for the source lemma. -/
theorem clockValueInv_refBlockHeap {width : Nat} [NeZero width] (ck : Nat) (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (inv : refBlockInv heap heap2) :
    ∀ (value : Value) (address : HeapAddress (WordLocW width)),
      ClockValueInv ck conf value refs (address, f, tf, heap) →
      ClockValueInv ck conf value refs (address, f, tf, heap2) := by
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro value address related
    cases related with
    | numberSmall _ _ i _ _ _ _ small => exact .numberSmall ck conf i refs f tf heap2 small
    | numberBig _ _ i ptr _ _ _ _ large found =>
      apply ClockValueInv.numberBig ck conf i ptr refs f tf heap2 large
      apply inv.1 ptr _ ⟨found, ?_⟩
      simp [isRefBlock, bignumRep, refBlock]
    | word64 _ _ word ptr _ _ _ _ found =>
      apply ClockValueInv.word64 ck conf word ptr refs f tf heap2
      apply inv.1 ptr _ ⟨found, ?_⟩
      unfold word64Rep
      split <;> simp [isRefBlock, refBlock]
    | codePtr _ _ n _ _ _ _ => exact .codePtr ck conf n refs f tf heap2
    | refPtr bit _ _ n _ _ _ _ domain notThunk notMut =>
      exact .refPtr bit ck conf n refs f tf heap2 domain notThunk notMut
    | refPtrThunk _ _ mode n body x _ _ _ _ found evaluated domain cell recursive =>
      refine .refPtrThunk ck conf mode n body x refs f tf heap2 found evaluated domain ?_ ?_
      · apply inv.1 _ _ ⟨cell, ?_⟩
        simp [isRefBlock, thunkBlock, refBlock]
      · intro positive
        exact ih (ck - 1) (by omega) body x (recursive positive)
    | refPtrThunkInlined _ _ n body x _ _ _ _ found notThunk recursive =>
      refine .refPtrThunkInlined ck conf n body address refs f tf heap2 found notThunk ?_
      intro positive
      exact ih (ck - 1) (by omega) body address (recursive positive)
    | blockNil _ _ stamp tag values _ _ _ _ empty bound zero =>
      exact .blockNil ck conf stamp tag values refs f tf heap2 empty bound zero
    | blockCons _ _ stamp tag ptr values xs _ _ _ _ nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag ptr values xs refs f tf heap2 nonempty ?_ timestamp ?_
      · intro positive
        apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
        apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
        intro child addr childInv
        exact ih (ck - 1) (by omega) child addr childInv
      · apply inv.1 ptr _ ⟨cell, ?_⟩
        simp [isRefBlock, blockRep, refBlock]

/-- Inserting a value array cannot turn a value that is not a thunk into a
thunk. An invalid reference at the insertion key becomes non-thunk as well. -/
theorem destThunk_notThunk_insertValueArray (value : Value) (refs : Spt (BvlSem.Ref Value))
    (ptr : Nat) (values : List Value)
    (notThunk : destThunk value refs = .notThunk) :
    destThunk value (sptInsert ptr (.valueArray values) refs) = .notThunk := by
  cases value with
  | refPtr bit index =>
    by_cases same : index = ptr
    · subst index
      simp [destThunk, sptLookup_sptInsert_same]
    · simpa [destThunk, sptLookup_sptInsert_ne ptr index _ refs same] using notThunk
  | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]

/-- Inserting a value array leaves the pointer annotation unchanged when the
previous cell was absent or another value array. -/
theorem refPtrAnnot_insertValueArray {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (ptr index : Nat) (values : List Value)
    (safe : sptLookup ptr refs = none ∨ ∃ oldValues,
      sptLookup ptr refs = some (.valueArray oldValues)) :
    refPtrAnnot (width := width) conf (sptLookup index (sptInsert ptr (.valueArray values) refs)) =
      refPtrAnnot conf (sptLookup index refs) := by
  by_cases same : index = ptr
  · subst index
    rcases safe with absent | ⟨oldValues, present⟩
    · simp [sptLookup_sptInsert_same, absent, refPtrAnnot]
    · simp [sptLookup_sptInsert_same, present, refPtrAnnot]
  · rw [sptLookup_sptInsert_ne ptr index _ refs same]

/-- An existing thunk survives insertion at a different key; the overwritten
cell cannot be a thunk under the value-array side condition. -/
theorem lookupThunk_insertValueArray (refs : Spt (BvlSem.Ref Value)) (ptr index : Nat)
    (values : List Value) (mode : AstHOL.ThunkMode) (body : Value)
    (safe : sptLookup ptr refs = none ∨ ∃ oldValues,
      sptLookup ptr refs = some (.valueArray oldValues))
    (found : sptLookup index refs = some (.thunk mode body)) :
    sptLookup index (sptInsert ptr (.valueArray values) refs) = some (.thunk mode body) := by
  by_cases same : index = ptr
  · subst index
    rcases safe with absent | ⟨oldValues, present⟩ <;> simp_all
  · simpa [sptLookup_sptInsert_ne ptr index _ refs same] using found

/-- The clocked value relation survives inserting a value-array reference.
This is a proof-side step toward the source theorem, retaining its crucial
condition that an existing cell at the insertion key is already a value array. -/
theorem clockValueInv_insertValueArray {width : Nat} [NeZero width] (ck : Nat)
    (conf : Config) (refs : Spt (BvlSem.Ref Value)) (ptr : Nat) (values : List Value)
    (safe : sptLookup ptr refs = none ∨ ∃ oldValues,
      sptLookup ptr refs = some (.valueArray oldValues)) :
    ∀ (value : Value) (context : ValueContext width), ClockValueInv ck conf value refs context →
      ClockValueInv ck conf value (sptInsert ptr (.valueArray values) refs) context := by
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro value context related
    cases related with
    | numberSmall _ _ i _ f tf heap small => exact .numberSmall ck conf i _ f tf heap small
    | numberBig _ _ i address _ f tf heap large found => exact .numberBig ck conf i address _ f tf heap large found
    | word64 _ _ word address _ f tf heap found => exact .word64 ck conf word address _ f tf heap found
    | codePtr _ _ n _ f tf heap => exact .codePtr ck conf n _ f tf heap
    | refPtr bit _ _ n _ f tf heap domain notThunk notMut =>
      have ann := refPtrAnnot_insertValueArray (width := width) conf refs ptr n values safe
      rw [← ann]
      apply ClockValueInv.refPtr bit ck conf n _ f tf heap domain
      · intro mode body
        by_cases same : n = ptr
        · subst n; simp [sptLookup_sptInsert_same]
        · simpa [sptLookup_sptInsert_ne ptr n _ refs same] using notThunk mode body
      · intro tag finalised left body right lookup
        by_cases same : n = ptr
        · subst n; simp [sptLookup_sptInsert_same] at lookup
        · exact notMut tag finalised left body right (by simpa [sptLookup_sptInsert_ne ptr n _ refs same] using lookup)
    | refPtrThunk _ _ mode n body x _ f tf heap found evaluated domain cell recursive =>
      refine .refPtrThunk ck conf mode n body x _ f tf heap
        (lookupThunk_insertValueArray refs ptr n values mode body safe found)
        (fun h => destThunk_notThunk_insertValueArray body refs ptr values (evaluated h)) domain cell ?_
      intro positive
      exact ih (ck - 1) (by omega) body _ (recursive positive)
    | refPtrThunkInlined _ _ n body x _ f tf heap found notThunk recursive =>
      refine .refPtrThunkInlined ck conf n body x _ f tf heap
        (lookupThunk_insertValueArray refs ptr n values .evaluated body safe found)
        (destThunk_notThunk_insertValueArray body refs ptr values notThunk) ?_
      intro positive
      exact ih (ck - 1) (by omega) body _ (recursive positive)
    | blockNil _ _ stamp tag values _ f tf heap empty bound zero =>
      exact .blockNil ck conf stamp tag values _ f tf heap empty bound zero
    | blockCons _ _ stamp tag address values xs _ f tf heap nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag address values xs _ f tf heap nonempty ?_ timestamp cell
      intro positive
      apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
      apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
      intro child x childInv
      exact ih (ck - 1) (by omega) child _ childInv


/-- A value invariant is preserved by replacing a value-array reference and
changing only reference-block heap cells. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_ValueArray_insert"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_insertValueArray {width : Nat} [NeZero width] (conf : Config)
    (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (address : HeapAddress (WordLocW width))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) (ptr : Nat)
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (heap2 : ValueHeap width)
    (valid : refBlockInv heap heap2 ∧ valueInv conf value refs (address, f, tf, heap) ∧
      (sptMem ptr refs → ∃ oldValues, sptLookup ptr refs = some (.valueArray oldValues))) :
    valueInv conf value (sptInsert ptr (.valueArray values) refs) (address, f, tf, heap2) := by
  have safe : sptLookup ptr refs = none ∨ ∃ oldValues,
      sptLookup ptr refs = some (.valueArray oldValues) := by
    by_cases absent : sptLookup ptr refs = none
    · exact Or.inl absent
    · apply Or.inr
      apply valid.2.2
      cases found : sptLookup ptr refs with
      | none => exact False.elim (absent found)
      | some cell => simp [sptMem, sptDomain, found]
  intro ck
  have inserted := clockValueInv_insertValueArray ck conf refs ptr values safe value (address, f, tf, heap) (valid.2.1 ck)
  exact clockValueInv_refBlockHeap ck conf _ f tf heap heap2 valid.1 value address inserted

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
