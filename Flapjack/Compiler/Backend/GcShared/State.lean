import Flapjack.Compiler.Backend.GcShared

/-! The shared abstract generational collector state. -/
namespace Flapjack.Compiler.Backend

/-- Abstract state shared by the generational collectors. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "gc_state"]
structure GcState (α β : Type) where
  old : List (HeapElement α β)
  h1 : List (HeapElement α β)
  h2 : List (HeapElement α β)
  r4 : List (HeapElement α β)
  r3 : List (HeapElement α β)
  r2 : List (HeapElement α β)
  r1 : List (HeapElement α β)
  a : Nat
  n : Nat
  ok : Bool
  heap : List (HeapElement α β)
  heap0 : List (HeapElement α β)

/-- Initial state before a generational collection. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "empty_state_def"]
def emptyGcState {α β : Type} : GcState α β :=
  ⟨[], [], [], [], [], [], [], 0, 0, true, [], []⟩

/-- Split a heap at two element boundaries. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_segment_def"]
def heapSegment {α β : Type} (bounds : Nat × Nat) (heap : List (HeapElement α β)) :
    Option (List (HeapElement α β) × List (HeapElement α β) × List (HeapElement α β)) :=
  let (a, b) := bounds
  match heapSplit a heap with
  | none => none
  | some (first, remaining) =>
    if b < a then none else
      (heapSplit (b - heapLength first) remaining).map fun (middle, last) => (first, middle, last)

end Flapjack.Compiler.Backend
