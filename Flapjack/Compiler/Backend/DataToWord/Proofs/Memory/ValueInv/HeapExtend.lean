module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv
public import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup
public import Flapjack.Compiler.Backend.GcShared.HeapSimilarity

@[expose] public section

/-! Preservation of value representations when the abstract heap grows. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Existing value representations survive adding heap cells and timestamp
mappings, provided existing successful lookups remain unchanged. This is
Flapjack infrastructure for constructor allocation. -/
theorem clockValueInv_heapExtend {width : Nat} [NeZero width] (ck : Nat)
    (conf : Config) (refs : Spt (BvlSem.Ref Value))
    (f tf tf' : HolFiniteMapExact Nat Nat) (heap heap' : ValueHeap width)
    (timestamps : ∀ n ptr, tf.lookup n = some ptr → tf'.lookup n = some ptr)
    (cells : ∀ ptr cell, isDataElement cell → heapLookup ptr heap = some cell → heapLookup ptr heap' = some cell) :
    ∀ (value : Value) (address : HeapAddress (WordLocW width)),
      ClockValueInv ck conf value refs (address, f, tf, heap) →
      ClockValueInv ck conf value refs (address, f, tf', heap') := by
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro value address related
    cases related with
    | numberSmall _ _ i _ _ _ _ small => exact .numberSmall ck conf i refs f tf' heap' small
    | numberBig _ _ i ptr _ _ _ _ large found => exact .numberBig ck conf i ptr refs f tf' heap' large (cells ptr _ (by simp [isDataElement, bignumRep]) found)
    | word64 _ _ word ptr _ _ _ _ found => exact .word64 ck conf word ptr refs f tf' heap' (cells ptr _ (by simp [isDataElement, word64Rep]; split <;> simp) found)
    | codePtr _ _ n _ _ _ _ => exact .codePtr ck conf n refs f tf' heap'
    | refPtr bit _ _ n _ _ _ _ domain notThunk notMut =>
      exact .refPtr bit ck conf n refs f tf' heap' domain notThunk notMut
    | refPtrThunk _ _ mode n body x _ _ _ _ found evaluated domain cell recursive =>
      refine .refPtrThunk ck conf mode n body x refs f tf' heap' found evaluated domain (cells _ _ (by simp [isDataElement, thunkBlock]) cell) ?_
      intro positive
      exact ih (ck - 1) (by omega) body x (recursive positive)
    | refPtrThunkInlined _ _ n body x _ _ _ _ found notThunk recursive =>
      refine .refPtrThunkInlined ck conf n body address refs f tf' heap' found notThunk ?_
      intro positive
      exact ih (ck - 1) (by omega) body address (recursive positive)
    | blockNil _ _ stamp tag values _ _ _ _ empty bound zero =>
      exact .blockNil ck conf stamp tag values refs f tf' heap' empty bound zero
    | blockCons _ _ stamp tag ptr values xs _ _ _ _ nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag ptr values xs refs f tf' heap' nonempty ?_
        (timestamps stamp ptr timestamp) (cells ptr _ (by simp [isDataElement, blockRep]) cell)
      intro positive
      apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
      apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
      intro child x childInv
      exact ih (ck - 1) (by omega) child x childInv

/-- Heap and timestamp-map extension preserves the unbounded value relation. -/
theorem valueInv_heapExtend {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf tf' : HolFiniteMapExact Nat Nat) (heap heap' : ValueHeap width)
    (timestamps : ∀ n ptr, tf.lookup n = some ptr → tf'.lookup n = some ptr)
    (cells : ∀ ptr cell, isDataElement cell → heapLookup ptr heap = some cell → heapLookup ptr heap' = some cell)
    (value : Value) (address : HeapAddress (WordLocW width))
    (related : valueInv conf value refs (address, f, tf, heap)) :
    valueInv conf value refs (address, f, tf', heap') := by
  intro ck
  exact clockValueInv_heapExtend ck conf refs f tf tf' heap heap' timestamps cells value address (related ck)

/-- Replacing an unused region by an equally sized allocation preserves every
old data-cell lookup. Interior offsets of the old unused region have no cell. -/
theorem heapLookup_allocate_preservesData {α β : Type}
    (pre post replacement : List (HeapElement α β)) (unused : Nat)
    (size : heapLength replacement = unused + 1) (offset : Nat) (cell : HeapElement α β)
    (data : isDataElement cell)
    (found : heapLookup offset (pre ++ [.unused unused] ++ post) = some cell) :
    heapLookup offset (pre ++ replacement ++ post) = some cell := by
  have old := found
  simp only [List.append_assoc, List.singleton_append] at old ⊢
  rw [Flapjack.Compiler.Backend.GenGc.heapLookup_append] at old ⊢
  by_cases before : offset < heapLength pre
  · simpa [before] using old
  · simp only [before, ↓reduceIte] at old ⊢
    rw [Flapjack.Compiler.Backend.GenGc.heapLookup_append]
    by_cases inside : offset - heapLength pre < unused + 1
    · by_cases zero : offset - heapLength pre = 0
      · simp [heapLookup, zero] at old
        subst cell
        simp [isDataElement] at data
      · have positive : offset - heapLength pre < elLength (HeapElement.unused unused : HeapElement α β) := by
          simpa [elLength] using inside
        simp [heapLookup, zero, positive] at old
    · have after : ¬ offset - heapLength pre < heapLength replacement := by simpa [size] using inside
      simp only [after, ↓reduceIte]
      have oldAfter : ¬ offset - heapLength pre < elLength (HeapElement.unused unused : HeapElement α β) := by
        simpa [elLength] using inside
      have nonzero : offset - heapLength pre ≠ 0 := by omega
      simpa [heapLookup, nonzero, oldAfter, elLength, size, inside] using old

/-- Allocating a nonempty constructor in unused space preserves all previous
value representations and gives the new block its own representation. The
field values may share existing cells. -/
theorem valueInv_allocateBlock {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (pre post remainder : ValueHeap width) (unused next tag : Nat)
    (values : List Value) (addresses : List (HeapAddress (WordLocW width)))
    (nonempty : values ≠ [])
    (size : heapLength (blockRep tag addresses :: remainder) = unused + 1)
    (bound : ∀ n ptr, tf.lookup n = some ptr → n < next)
    (fields : List.Forall₂ (fun value address =>
      valueInv conf value refs (address, f, tf, pre ++ [.unused unused] ++ post)) values addresses) :
    let newHeap := pre ++ (blockRep tag addresses :: remainder) ++ post
    let newTf := tf.update (next, heapLength pre)
    (∀ value address, valueInv conf value refs (address, f, tf, pre ++ [.unused unused] ++ post) →
      valueInv conf value refs (address, f, newTf, newHeap)) ∧
    valueInv conf (.block next tag values) refs
      (.pointer (heapLength pre) (.word (ptrBits conf tag addresses.length)), f, newTf, newHeap) := by
  dsimp only
  have timestamps : ∀ n ptr, tf.lookup n = some ptr →
      (tf.update (next, heapLength pre)).lookup n = some ptr := by
    intro n ptr lookup
    have below := bound n ptr lookup
    have different : next ≠ n := by omega
    simpa [HolFiniteMapExact.update, FUPDATE, different] using lookup
  have cells : ∀ ptr cell, isDataElement cell →
      heapLookup ptr (pre ++ [.unused unused] ++ post) = some cell →
      heapLookup ptr (pre ++ (blockRep tag addresses :: remainder) ++ post) = some cell := by
    intro ptr cell data found
    exact heapLookup_allocate_preservesData pre post (blockRep tag addresses :: remainder) unused size ptr cell data found
  constructor
  · intro value address related
    exact valueInv_heapExtend conf refs f tf _ _ _ timestamps cells value address related
  · apply (valueInv_nonemptyBlock conf next tag values refs _ f _ _ nonempty).mpr
    refine ⟨heapLength pre, addresses, ?_, ?_, rfl, ?_⟩
    · exact fields.imp (fun value address related =>
        valueInv_heapExtend conf refs f tf _ _ _ timestamps cells value address related)
    · simp [HolFiniteMapExact.update, FUPDATE]
    · simpa only [List.append_assoc, List.cons_append] using
        Flapjack.Compiler.Backend.heapLookup_prefix pre (remainder ++ post) (blockRep tag addresses)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
