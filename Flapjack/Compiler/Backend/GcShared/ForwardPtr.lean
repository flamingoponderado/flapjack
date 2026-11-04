import Flapjack.Compiler.Backend.GcShared

/-! Status preservation for abstract forwarding-pointer updates. -/
namespace Flapjack.Compiler.Backend

/-- Replacing the data element at a heap prefix preserves the rest of the
heap and carries the original status through unchanged. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "gc_forward_ptr_thm"]
theorem gcForwardPtr_thm {α β : Type} (before after : List (HeapElement α β))
    (ys : List (HeapAddress α)) (len : Nat) (data : β)
    (address : Nat) (value : α) (ok : Bool) :
    gcForwardPtr (heapLength before) (before ++ .dataElement ys len data :: after) address value ok =
      (before ++ .forwardPointer address value len :: after, ok) := by
  induction before with
  | nil => simp [gcForwardPtr, heapLength, elLength]
  | cons head tail ih =>
    simp only [List.cons_append, heapLength, List.map_cons, List.sum_cons]
    have positive : 0 < elLength head := by cases head <;> simp [elLength]
    simp only [gcForwardPtr]
    have nonzero : elLength head + (List.map elLength tail).sum ≠ 0 := by omega
    have notInside : ¬ elLength head + (List.map elLength tail).sum < elLength head := by omega
    simp only [nonzero, notInside, ↓reduceIte]
    have sub : elLength head + (List.map elLength tail).sum - elLength head = heapLength tail := by
      simp [heapLength]
    rw [sub, ih]

@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "gc_forward_ptr_ok"]
theorem gcForwardPtr_ok {α β : Type} (heap : List (HeapElement α β))
    (offset address : Nat) (value : α) (ok : Bool) (result : List (HeapElement α β))
    (run : gcForwardPtr offset heap address value ok = (result, true)) : ok = true := by
  induction heap generalizing offset result with
  | nil => simp [gcForwardPtr] at run
  | cons head tail ih =>
    simp only [gcForwardPtr] at run
    split at run
    · cases head <;> simp_all
    · split at run
      · simp at run
      · cases next : gcForwardPtr (offset - elLength head) tail address value ok with
        | mk tail' status =>
          simp only [next, Prod.mk.injEq] at run
          obtain ⟨_, rfl⟩ := run
          exact ih _ tail' next

end Flapjack.Compiler.Backend
