import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Abstract

/-! Heap-shape preservation for byte-array payload updates. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- Two heap cells have the same layout and pointer fields, allowing their
data payloads to differ. -/
inductive HeapCellShape {α β : Type} : HeapElement α β → HeapElement α β → Prop where
  | unused (n) : HeapCellShape (.unused n) (.unused n)
  | forward (n addr ptr) : HeapCellShape (.forwardPointer n addr ptr) (.forwardPointer n addr ptr)
  | data (ptrs n before after) : HeapCellShape (.dataElement ptrs n before) (.dataElement ptrs n after)

/-- Related heap cells have equal allocated lengths. -/
theorem HeapCellShape.length {α β : Type} {left right : HeapElement α β} (h : HeapCellShape left right) :
    elLength left = elLength right := by cases h <;> rfl

/-- Related heap cells agree on whether they are data cells. -/
theorem HeapCellShape.isData {α β : Type} {left right : HeapElement α β} (h : HeapCellShape left right) :
    isDataElement left ↔ isDataElement right := by cases h <;> simp [isDataElement]

/-- Same-layout heaps retain their total allocated length. -/
theorem heapLength_shape {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) : heapLength left = heapLength right := by
  induction shape with
  | nil => rfl
  | @cons x y xs ys head tail ih =>
    change elLength x + heapLength xs = elLength y + heapLength ys
    rw [head.length, ih]

/-- Looking up an unused cell yields the same result in same-layout heaps. -/
theorem heapLookup_unused_shape {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) (offset n : Nat) :
    heapLookup offset left = some (.unused n) ↔ heapLookup offset right = some (.unused n) := by
  induction shape generalizing offset with
  | nil => simp [heapLookup]
  | @cons x y xs ys head tail ih =>
    by_cases zero : offset = 0
    · subst offset
      cases head <;> simp [heapLookup]
    · by_cases inside : offset < elLength x
      · have inside' : offset < elLength y := by rw [← head.length]; exact inside
        simp [heapLookup, zero, inside, inside']
      · have inside' : ¬ offset < elLength y := by rw [← head.length]; exact inside
        simp only [heapLookup, zero, inside, inside', ↓reduceIte]
        rw [← head.length]
        exact ih _

/-- A lookup is a data cell in one layout exactly when it is in the other. -/
theorem heapLookup_data_shape {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) (offset : Nat) :
    isSomeDataElement (heapLookup offset left) ↔ isSomeDataElement (heapLookup offset right) := by
  induction shape generalizing offset with
  | nil => simp [heapLookup, isSomeDataElement]
  | @cons x y xs ys head tail ih =>
    by_cases zero : offset = 0
    · subst offset
      cases head <;> simp [heapLookup, isSomeDataElement]
    · by_cases inside : offset < elLength x
      · have inside' : offset < elLength y := by rw [← head.length]; exact inside
        simp [heapLookup, zero, inside, inside', isSomeDataElement]
      · have inside' : ¬ offset < elLength y := by rw [← head.length]; exact inside
        simp only [heapLookup, zero, inside, inside', ↓reduceIte]
        rw [← head.length]
        exact ih _

/-- Heap splitting preserves the cell layout in both resulting segments. -/
theorem heapSplit_shape {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) (offset : Nat)
    (pre post : List (HeapElement α β)) (split : heapSplit offset left = some (pre, post)) :
    ∃ pre' post', heapSplit offset right = some (pre', post') ∧
      List.Forall₂ HeapCellShape pre pre' ∧ List.Forall₂ HeapCellShape post post' := by
  induction shape generalizing offset pre post with
  | nil =>
    by_cases zero : offset = 0
    · subst offset
      simp [heapSplit] at split
      obtain ⟨rfl, rfl⟩ := split
      exact ⟨[], [], by simp [heapSplit], .nil, .nil⟩
    · simp [heapSplit, zero] at split
  | @cons x y xs ys head tail ih =>
    by_cases zero : offset = 0
    · subst offset
      simp [heapSplit] at split
      obtain ⟨rfl, rfl⟩ := split
      exact ⟨[], y :: ys, by simp [heapSplit], .nil, .cons head tail⟩
    · by_cases inside : offset < elLength x
      · simp [heapSplit, zero, inside] at split
      · have inside' : ¬ offset < elLength y := by rw [← head.length]; exact inside
        cases tailSplit : heapSplit (offset - elLength x) xs with
        | none => simp [heapSplit, zero, inside, tailSplit] at split
        | some pair =>
          obtain ⟨leftPrefix, leftSuffix⟩ := pair
          have pairEq : (x :: leftPrefix, leftSuffix) = (pre, post) := by
            simpa [heapSplit, zero, inside, tailSplit] using split
          cases pairEq
          obtain ⟨rightPrefix, rightSuffix, rightSplit, preShape, sufShape⟩ :=
            ih (offset - elLength x) leftPrefix post tailSplit
          refine ⟨y :: rightPrefix, rightSuffix, ?_, .cons head preShape, sufShape⟩
          simp only [heapSplit, zero, inside', ↓reduceIte]
          rw [← head.length, rightSplit]
          rfl

/-- Same-layout lists preserve the data-cell property. -/
theorem heapShape_allData {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right)
    (allData : ∀ x ∈ left, isDataElement x) : ∀ x ∈ right, isDataElement x := by
  induction shape with
  | nil => simp
  | @cons x y xs ys head tail ih =>
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rest
    · exact head.isData.mp (allData x (by simp))
    · apply ih
      · intro v hv
        exact allData v (by simp [hv])
      · exact rest

/-- A data-only prefix remains data-only under a same-layout update. -/
theorem dataUpTo_shape {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) (offset : Nat)
    (data : dataUpTo offset left) : dataUpTo offset right := by
  obtain ⟨pre, post, split, allData⟩ := data
  obtain ⟨pre', post', split', preShape, _⟩ := heapSplit_shape shape offset pre post split
  refine ⟨pre', post', split', ?_⟩
  exact heapShape_allData preShape allData

/-- Unused-space bookkeeping survives an update that preserves the heap layout. -/
theorem unusedSpaceInv_shape {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) (offset length : Nat)
    (unused : unusedSpaceInv offset length left) : unusedSpaceInv offset length right := by
  refine ⟨?_, ?_, dataUpTo_shape shape offset unused.2.2⟩
  · intro nonzero
    exact (heapLookup_unused_shape shape offset (length - 1)).mp (unused.1 nonzero)
  · rw [← heapLength_shape shape]
    exact unused.2.1

/-- Root pointers remain valid when heap cell layout is preserved. -/
theorem rootsOk_shape {α β γ : Type} (roots : List (HeapAddress α))
    {left right : List (HeapElement β γ)} (shape : List.Forall₂ HeapCellShape left right)
    (valid : rootsOk roots left) : rootsOk roots right := by
  intro ptr value member
  exact (heapLookup_data_shape shape ptr).mp (valid ptr value member)

/-- Preserving cell layout preserves the list of forwarding pointers. -/
theorem heapShape_forwardPointers {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) :
    left.filter isForwardPointer = right.filter isForwardPointer := by
  induction shape with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp only [List.filter_cons, isForwardPointer, ↓reduceIte, ih] <;> rfl

/-- Every data cell in a same-layout replacement has a predecessor with the
same child pointers and allocated size. -/
theorem heapShape_dataMember {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) (ptrs : List (HeapAddress α))
    (size : Nat) (data : β) (member : .dataElement ptrs size data ∈ right) :
    ∃ oldData, .dataElement ptrs size oldData ∈ left := by
  induction shape with
  | nil => simp at member
  | @cons x y xs ys head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with same | rest
    · subst y
      cases head with
      | data _ _ before _ => exact ⟨before, by simp⟩
    · obtain ⟨oldData, present⟩ := ih rest
      exact ⟨oldData, by simp [present]⟩

/-- Heap validity depends on pointer layout, rather than data-cell payloads. -/
theorem heapOk_shape {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) (limit : Nat)
    (valid : heapOk left limit) : heapOk right limit := by
  refine ⟨(heapLength_shape shape).symm.trans valid.1, ?_, ?_⟩
  · rw [← heapShape_forwardPointers shape]
    exact valid.2.1
  · intro ptrs size data ptr value h
    obtain ⟨oldData, oldMember⟩ := heapShape_dataMember shape ptrs size data h.1
    exact (heapLookup_data_shape shape ptr).mp (valid.2.2 ptrs size oldData ptr value ⟨oldMember, h.2⟩)

/-- Generation-start pointer restrictions depend only on heap layout. -/
theorem genStartOk_shape {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) (refsStart genStart : Nat)
    (valid : genStartOk left refsStart genStart) : genStartOk right refsStart genStart := by
  obtain ⟨pre, post, split, pointers⟩ := valid
  obtain ⟨pre', post', split', preShape, _⟩ := heapSplit_shape shape genStart pre post split
  refine ⟨pre', post', split', ?_⟩
  intro xs len data ptr value h
  obtain ⟨oldData, oldMember⟩ := heapShape_dataMember preShape xs len data h.1
  exact pointers xs len oldData ptr value ⟨oldMember, h.2⟩

/-- Generation-state validity is preserved by same-layout replacement. -/
theorem genStateOk_shape {α β : Type} {left right : List (HeapElement α β)}
    (shape : List.Forall₂ HeapCellShape left right) (a refsStart : Nat) (gens : GcCombined.GenState)
    (valid : genStateOk a refsStart left gens) : genStateOk a refsStart right gens := by
  cases gens with
  | genState _ starts =>
    exact ⟨valid.1, fun start member => genStartOk_shape shape refsStart start (valid.2 start member)⟩

/-- Every heap cell has the same layout as itself. -/
theorem HeapCellShape.refl {α β : Type} (cell : HeapElement α β) : HeapCellShape cell cell := by
  cases cell with
  | unused n => exact .unused n
  | forwardPointer n addr ptr => exact .forward n addr ptr
  | dataElement ptrs n data => exact .data ptrs n data data

/-- Repacking a byte payload leaves the cell's pointer fields and size unchanged. -/
theorem bytesRep_shape {width : Nat} [NeZero width] (be flag : Bool)
    (before after : List (BitVec 8)) (words : List (BitVec width)) :
    HeapCellShape (bytesRep be flag before words) (bytesRep be flag after words) := by
  simp only [bytesRep, writeBytes_wordCount]
  exact .data [] words.length _ _

/-- Byte payload replacement in a heap leaves every cell's layout unchanged. -/
theorem byteHeap_shape {width : Nat} [NeZero width] (be flag : Bool)
    (before after : List (BitVec 8)) (words : List (BitVec width))
    (pre post : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) :
    List.Forall₂ HeapCellShape (pre ++ [bytesRep be flag before words] ++ post)
      (pre ++ [bytesRep be flag after words] ++ post) := by
  have self (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) :
      List.Forall₂ HeapCellShape heap heap := by
    induction heap with
    | nil => exact .nil
    | cons head tail ih => exact .cons (HeapCellShape.refl head) ih
  induction pre with
  | nil => exact .cons (bytesRep_shape be flag before after words) (self post)
  | cons head tail ih => exact .cons (HeapCellShape.refl head) ih

/-- The original byte-payload replacement preserves the unused-space
invariant. This independently checked statement is infrastructure for the
larger heap-update theorem; the original local HOL lemma is not tagged here. -/
theorem unusedSpaceInv_byteUpdate {width : Nat} [NeZero width] (be flag : Bool)
    (before after : List (BitVec 8)) (words : List (BitVec width))
    (pre post : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (offset length : Nat)
    (unused : unusedSpaceInv offset length (pre ++ [bytesRep be flag before words] ++ post)) :
    unusedSpaceInv offset length (pre ++ [bytesRep be flag after words] ++ post) :=
  unusedSpaceInv_shape (byteHeap_shape be flag before after words pre post) offset length unused

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
