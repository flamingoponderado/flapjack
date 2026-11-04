import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateHeap
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateValue

/-! Value invariants across replacement of a byte-array heap cell. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Heap-cell predicate excluding byte-tagged data cells. -/
def nonByteCell {α β : Type} : HeapElement α (HeapTag × β) → Prop
  | .dataElement _ _ (.bytesTag _ _, _) => False
  | _ => True

/-- Lookup of any selected cell is unchanged if related heaps preserve layout
and preserve every selected cell. -/
theorem heapLookup_preserve_selected {α β : Type} (selected : HeapElement α β → Prop)
    {left right : List (HeapElement α β)}
    (shape : List.Forall₂ (fun x y => HeapCellShape x y ∧ (selected x → x = y)) left right)
    (offset : Nat) (cell : HeapElement α β) (found : heapLookup offset left = some cell)
    (select : selected cell) : heapLookup offset right = some cell := by
  induction shape generalizing offset with
  | nil => simp [heapLookup] at found
  | @cons x y xs ys head tail ih =>
    by_cases zero : offset = 0
    · subst offset
      simp only [heapLookup, ↓reduceIte, Option.some.injEq] at found
      subst x
      rw [← head.2 select]
      simp [heapLookup]
    · by_cases inside : offset < elLength x
      · simp [heapLookup, zero, inside] at found
      · have insideRight : ¬ offset < elLength y := by rw [← head.1.length]; exact inside
        simp only [heapLookup, zero, inside, ↓reduceIte] at found
        simp only [heapLookup, zero, insideRight, ↓reduceIte]
        rw [← head.1.length]
        exact ih _ found

/-- Replacing a byte array preserves every non-byte heap-cell lookup. -/
theorem heapLookup_byteHeap_nonByte {width : Nat} [NeZero width] (be flag : Bool)
    (before after : List (BitVec 8)) (words : List (BitVec width))
    (pre post : ValueHeap width) (offset : Nat) (cell : HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))
    (found : heapLookup offset (pre ++ [bytesRep be flag before words] ++ post) = some cell)
    (select : nonByteCell cell) :
    heapLookup offset (pre ++ [bytesRep be flag after words] ++ post) = some cell := by
  have self (heap : ValueHeap width) :
      List.Forall₂ (fun x y => HeapCellShape x y ∧ (nonByteCell x → x = y)) heap heap := by
    induction heap with
    | nil => exact .nil
    | cons head tail ih => exact .cons ⟨HeapCellShape.refl head, fun _ => rfl⟩ ih
  have shape : List.Forall₂ (fun x y => HeapCellShape x y ∧ (nonByteCell x → x = y))
      (pre ++ [bytesRep be flag before words] ++ post) (pre ++ [bytesRep be flag after words] ++ post) := by
    clear found
    induction pre with
    | nil =>
      refine .cons ⟨bytesRep_shape be flag before after words, ?_⟩ (self post)
      intro impossible
      simp [nonByteCell, bytesRep] at impossible
    | cons head tail ih => exact .cons ⟨HeapCellShape.refl head, fun _ => rfl⟩ ih
  exact heapLookup_preserve_selected nonByteCell shape offset cell found select

/-- The clocked value relation survives changing the payload of one byte cell.
The number, block, word and thunk cases only inspect non-byte heap cells. -/
theorem clockValueInv_byteHeap {width : Nat} [NeZero width] (ck : Nat) (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (pre post : ValueHeap width) (be flag : Bool) (before after : List (BitVec 8))
    (words : List (BitVec width)) :
    ∀ (value : Value) (address : HeapAddress (WordLocW width)),
      ClockValueInv ck conf value refs (address, f, tf, pre ++ [bytesRep be flag before words] ++ post) →
      ClockValueInv ck conf value refs (address, f, tf, pre ++ [bytesRep be flag after words] ++ post) := by
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro value address related
    cases related with
    | numberSmall _ _ i _ _ _ _ small => exact .numberSmall ck conf i refs f tf _ small
    | numberBig _ _ i ptr _ _ _ _ large found =>
      apply ClockValueInv.numberBig ck conf i ptr refs f tf _ large
      exact heapLookup_byteHeap_nonByte be flag before after words pre post ptr _ found (by simp [nonByteCell, bignumRep])
    | word64 _ _ word ptr _ _ _ _ found =>
      apply ClockValueInv.word64 ck conf word ptr refs f tf _
      apply heapLookup_byteHeap_nonByte be flag before after words pre post ptr _ found
      unfold word64Rep
      split <;> simp [nonByteCell]
    | codePtr _ _ n _ _ _ _ => exact .codePtr ck conf n refs f tf _
    | refPtr bit _ _ n _ _ _ _ domain notThunk notMut =>
      exact .refPtr bit ck conf n refs f tf _ domain notThunk notMut
    | refPtrThunk _ _ mode n body x _ _ _ _ found evaluated domain cell recursive =>
      refine .refPtrThunk ck conf mode n body x refs f tf _ found evaluated domain ?_ ?_
      · exact heapLookup_byteHeap_nonByte be flag before after words pre post _ _ cell (by simp [nonByteCell, thunkBlock])
      · intro positive
        exact ih (ck - 1) (by omega) body x (recursive positive)
    | refPtrThunkInlined _ _ n body x _ _ _ _ found notThunk recursive =>
      refine .refPtrThunkInlined ck conf n body address refs f tf _ found notThunk ?_
      intro positive
      exact ih (ck - 1) (by omega) body address (recursive positive)
    | blockNil _ _ stamp tag values _ _ _ _ empty bound zero =>
      exact .blockNil ck conf stamp tag values refs f tf _ empty bound zero
    | blockCons _ _ stamp tag ptr values xs _ _ _ _ nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag ptr values xs refs f tf _ nonempty ?_ timestamp ?_
      · intro positive
        apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
        apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
        intro child addr childInv
        exact ih (ck - 1) (by omega) child addr childInv
      · exact heapLookup_byteHeap_nonByte be flag before after words pre post _ _ cell (by simp [nonByteCell, blockRep])

/-- A value invariant is unchanged by replacing a byte-array payload in the
heap. This is the source-local v_inv_IMP consequence, proved for every byte
list and destination word list. -/
theorem valueInv_byteHeap {width : Nat} [NeZero width] (conf : Config) (value : Value)
    (refs : Spt (BvlSem.Ref Value)) (address : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (pre post : ValueHeap width) (be flag : Bool)
    (before after : List (BitVec 8)) (words : List (BitVec width))
    (valid : valueInv conf value refs (address, f, tf, pre ++ [bytesRep be flag before words] ++ post)) :
    valueInv conf value refs (address, f, tf, pre ++ [bytesRep be flag after words] ++ post) := by
  intro ck
  exact clockValueInv_byteHeap ck conf refs f tf pre post be flag before after words value address (valid ck)

/-- Updating a source byte-array reference and its heap payload together
preserves the value relation. The heap-store and reference-cell invariants
remain separate obligations for the complete memory-update theorem. -/
theorem valueInv_byteUpdate {width : Nat} [NeZero width] (conf : Config) (value : Value)
    (refs : Spt (BvlSem.Ref Value)) (address : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (pre post : ValueHeap width) (be flag : Bool)
    (before after : List (BitVec 8)) (words : List (BitVec width))
    (ptr : Nat) (oldFlag : Bool) (oldBytes : List (BitVec 8))
    (found : sptLookup ptr refs = some (.byteArray oldFlag oldBytes))
    (valid : valueInv conf value refs (address, f, tf, pre ++ [bytesRep be flag before words] ++ post)) :
    valueInv conf value (sptInsert ptr (.byteArray flag after) refs)
      (address, f, tf, pre ++ [bytesRep be flag after words] ++ post) := by
  apply valueInv_byteHeap conf value (sptInsert ptr (.byteArray flag after) refs)
    address f tf pre post be flag before after words
  apply valueInv_insertByteArray conf value refs address f tf _ ptr flag after
  exact ⟨valid, fun _ => ⟨oldFlag, oldBytes, found⟩⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
