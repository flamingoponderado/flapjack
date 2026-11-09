module

public import Flapjack.Compiler.Backend.GenGcPartial

@[expose] public section

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

/-- Traversing roots preserves the heap's word length, including failure. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_list_heap_length"]
theorem gcMoveList_heapLength {α β : Type} (roots roots1 : List (HeapAddress α))
    (conf : Config β) (state state1 : GcState α β)
    (run : gcMoveList conf state roots = (roots1, state1)) :
    heapLength state.heap = heapLength state1.heap := by
  induction roots generalizing state roots1 state1 with
  | nil => simp [gcMoveList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons root roots ih =>
    simp only [gcMoveList] at run
    generalize headRun : gcMove conf state root = result at run
    obtain ⟨rootMid, middle⟩ := result
    generalize tailRun : gcMoveList conf middle roots = result at run
    obtain ⟨tail, final⟩ := result
    simp only [Prod.mk.injEq] at run
    obtain ⟨_, rfl⟩ := run
    exact (gcMove_heapLength conf state middle root rootMid headRun).trans
      (ih (state := middle) (roots1 := tail) (state1 := final) tailRun)

/-- Reference-object traversal preserves the heap's word length. The local HOL
proof has not yet been replayed. -/
@[hol "cakeml/compiler/backend/gc/gen_gc_partialScript.sml" "gc_move_ref_list_heap_length" 1123]
theorem gcMoveRefList_heapLength {α β γ : Type} (conf : Config γ)
    (refs refs1 : List (HeapElement α β)) (state state1 : GcState α γ)
    (run : gcMoveRefList conf state refs = (refs1, state1)) :
    heapLength state.heap = heapLength state1.heap := by
  induction refs generalizing state refs1 state1 with
  | nil => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
  | cons head tail ih =>
    cases head with
    | unused len => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    | forwardPointer ptr value len => simp [gcMoveRefList, Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; rfl
    | dataElement roots len payload =>
      simp only [gcMoveRefList] at run
      generalize headRun : gcMoveList conf state roots = result at run
      obtain ⟨roots1, middle⟩ := result
      generalize tailRun : gcMoveRefList conf middle tail = result at run
      obtain ⟨tail1, final⟩ := result
      simp only [Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      exact (gcMoveList_heapLength roots roots1 conf state middle headRun).trans
        (ih (state := middle) (refs1 := tail1) (state1 := final) tailRun)

end Flapjack.Compiler.Backend.GenGcPartial
