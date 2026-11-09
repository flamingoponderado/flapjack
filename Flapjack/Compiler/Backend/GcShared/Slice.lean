module

public import Flapjack.Compiler.Backend.GcShared.State
public import Flapjack.HolArb

@[expose] public section

/-! Heap slicing from the shared collector development. -/
namespace Flapjack.Compiler.Backend

/-- Drop a prefix ending at an element boundary; the source leaves an
invalid split unspecified. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_drop_def"]
noncomputable def heapDrop {α β : Type} (offset : Nat) (heap : List (HeapElement α β)) :
    List (HeapElement α β) :=
  match heapSplit offset heap with
  | none => holArb _
  | some (_, tail) => tail

/-- Take a prefix ending at an element boundary; the source leaves an
invalid split unspecified. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_take_def"]
noncomputable def heapTake {α β : Type} (offset : Nat) (heap : List (HeapElement α β)) :
    List (HeapElement α β) :=
  match heapSplit offset heap with
  | none => holArb _
  | some (head, _) => head

/-- A successful split identifies the prefix length and reconstructs the
whole heap. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_split_heap_length"]
theorem heapSplit_heapLength {α β : Type} (heap first second : List (HeapElement α β)) (offset : Nat)
    (split : heapSplit offset heap = some (first, second)) :
    heapLength first = offset ∧ heapLength (first ++ second) = heapLength heap ∧ first ++ second = heap := by
  induction heap generalizing first second offset with
  | nil =>
    simp only [heapSplit] at split
    split at split <;> simp_all [heapLength]
  | cons head tail ih =>
    simp only [heapSplit] at split
    split at split
    · simp only [Option.some.injEq, Prod.mk.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      simp_all [heapLength]
    · rename_i nonzero
      split at split
      · contradiction
      · rename_i notSmall
        cases sub : heapSplit (offset - elLength head) tail with
        | none => simp [sub] at split
        | some pair =>
          obtain ⟨first', second'⟩ := pair
          simp only [sub, Option.map_some, Option.some.injEq, Prod.mk.injEq] at split
          obtain ⟨rfl, rfl⟩ := split
          obtain ⟨prefixLen, _, reconstruct⟩ := ih first' second' _ sub
          subst tail
          simp only [heapLength, List.map_cons, List.sum_cons] at prefixLen ⊢
          refine ⟨?_, rfl, rfl⟩
          have lenPos : 0 < elLength head := by cases head <;> simp [elLength]
          omega

/-- A successful three-way split reconstructs the heap and records both
requested boundaries. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_segment_IMP"]
theorem heapSegment_imp {α β : Type} (heap : List (HeapElement α β)) (a b : Nat)
    (first middle last : List (HeapElement α β))
    (segment : heapSegment (a, b) heap = some (first, middle, last)) :
    first ++ middle ++ last = heap ∧ heapLength first = a ∧
      heapLength (first ++ middle) = b ∧ heapLength last = heapLength heap - b := by
  simp only [heapSegment] at segment
  cases firstSplit : heapSplit a heap with
  | none => simp [firstSplit] at segment
  | some pair =>
    obtain ⟨left, rest⟩ := pair
    simp only [firstSplit] at segment
    split at segment
    · contradiction
    · rename_i ordered
      cases secondSplit : heapSplit (b - heapLength left) rest with
      | none => simp [secondSplit] at segment
      | some pair =>
        obtain ⟨inside, suffix⟩ := pair
        simp only [secondSplit, Option.map_some, Option.some.injEq, Prod.mk.injEq] at segment
        obtain ⟨rfl, rfl, rfl⟩ := segment
        obtain ⟨firstLen, _, firstHeap⟩ := heapSplit_heapLength heap left rest a firstSplit
        obtain ⟨insideLen, _, secondHeap⟩ :=
          heapSplit_heapLength rest inside suffix (b - heapLength left) secondSplit
        subst rest
        subst heap
        simp only [List.append_assoc] at ⊢
        simp only [heapLength_append] at ⊢
        refine ⟨trivial, firstLen, ?_, ?_⟩ <;> omega

end Flapjack.Compiler.Backend
