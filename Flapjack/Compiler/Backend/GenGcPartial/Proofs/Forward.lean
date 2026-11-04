import Flapjack.Compiler.Backend.GenGcPartial

/-! Forwarding invariants for the partial generational collector. -/
namespace Flapjack.Compiler.Backend.GenGcPartial
open Flapjack Flapjack.Compiler.Backend

/-- Forwarding preserves the heap's word length even when it reports failure. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_forward_ptr_heap_length"]
theorem gcForwardPtr_heapLength {α β : Type} (offset : Nat) (heap : List (HeapElement α β))
    (address : Nat) (value : α) (ok : Bool) (result : List (HeapElement α β)) (ok' : Bool)
    (run : gcForwardPtr offset heap address value ok = (result, ok')) :
    heapLength heap = heapLength result := by
  induction heap generalizing offset result ok' with
  | nil => simp [gcForwardPtr, Prod.mk.injEq] at run; obtain ⟨rfl, _⟩ := run; rfl
  | cons head tail ih =>
    simp only [gcForwardPtr] at run
    split at run
    · simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, _⟩ := run
      simp only [heapLength, List.map_cons, List.sum_cons]
      cases head <;> simp [elLength]
    · split at run
      · simp only [Prod.mk.injEq] at run
        obtain ⟨rfl, _⟩ := run
        rfl
      · cases next : gcForwardPtr (offset - elLength head) tail address value ok with
        | mk resultTail status =>
          simp only [next, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have equal := ih _ resultTail status next
          simp only [heapLength, List.map_cons, List.sum_cons] at equal ⊢
          rw [equal]

/-- A partial root move preserves the original heap's word length. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_heap_length"]
theorem gcMove_heapLength {α β : Type} (conf : Config β) (state state1 : GcState α β)
    (root root1 : HeapAddress α) (run : gcMove conf state root = (root1, state1)) :
    heapLength state.heap = heapLength state1.heap := by
  cases root with
  | data value => simp [gcMove, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | pointer ptr value =>
    by_cases outside : ptr < conf.genStart ∨ conf.refsStart ≤ ptr
    · simp [gcMove, outside, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    · cases found : heapLookup ptr state.heap with
      | none => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
      | some element =>
        cases element with
        | unused len => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
        | forwardPointer dest old len => simp [gcMove, outside, found, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
        | dataElement roots len payload =>
          cases forward : gcForwardPtr ptr state.heap state.a value
              ((state.ok && decide (ptr < heapLength state.heap)) && decide (len + 1 ≤ state.n) && !(conf.isRef payload)) with
          | mk newHeap status =>
            simp only [gcMove, outside, ↓reduceIte, found, forward, Prod.mk.injEq] at run
            obtain ⟨_, rfl⟩ := run
            exact gcForwardPtr_heapLength ptr state.heap state.a value _ newHeap status forward

end Flapjack.Compiler.Backend.GenGcPartial
