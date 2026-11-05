import Flapjack.Compiler.Backend.GcShared.AddressMap
import Flapjack.Misc.FiniteMapApply

/-! Forwarding maps and heap element starting addresses. -/
namespace Flapjack.Compiler.Backend
open Flapjack

/-- Map the starting offset of each forwarding pointer to its target. Earlier
heap elements take precedence if an offset is repeated. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_map_def"
  (fmap_as_finite_support_result)]
def heapMap {α β : Type} (offset : Nat) : List (HeapElement α β) → HolFiniteMapExact Nat Nat
  | [] => HolFiniteMapExact.empty
  | .forwardPointer ptr _ len :: tail => (heapMap (offset + len + 1) tail).update (offset, ptr)
  | head :: tail => heapMap (offset + elLength head) tail

/-- Raw lookup counterpart of `heapMap`, used to check the finite-map codec. -/
def heapMapLookup {α β : Type} (offset : Nat) : List (HeapElement α β) → Nat → Option Nat
  | [] => fun _ => none
  | .forwardPointer ptr _ len :: tail => FUPDATE (heapMapLookup (offset + len + 1) tail) (offset, ptr)
  | head :: tail => heapMapLookup (offset + elLength head) tail

/-- The canonical forwarding map has the source-shaped raw lookup behavior. -/
theorem holFmapAsFiniteSupportResultWitness_heapMap {α β : Type} (offset : Nat)
    (heap : List (HeapElement α β)) (key : Nat) :
    (heapMap offset heap).lookup key = heapMapLookup offset heap key := by
  induction heap generalizing offset with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp [heapMap, heapMapLookup, HolFiniteMapExact.update, FUPDATE, ih]

/-- The forwarding map applied as HOL's total finite-map operation. The source
definition uses a finite map internally; it is not tagged until that internal
representation can be recorded by the reference infrastructure. -/
noncomputable def heapMap1 {α β : Type} (heap : List (HeapElement α β)) (address : Nat) : Nat :=
  holFapply (heapMap 0 heap) address

/-- Starting addresses of the elements of a heap, from a given base. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_addresses_def"]
def heapAddresses {α β : Type} (offset : Nat) : List (HeapElement α β) → Nat → Prop
  | [] => fun _ => False
  | head :: tail => fun address => address = offset ∨ heapAddresses (offset + elLength head) tail address

end Flapjack.Compiler.Backend
