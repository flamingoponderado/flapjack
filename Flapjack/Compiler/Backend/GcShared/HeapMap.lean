module

public import Flapjack.Compiler.Backend.GcShared.AddressMap
public import Flapjack.Misc.FiniteMapApply

@[expose] public section

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

/-- Addresses of a concatenation are the union of the two address ranges. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_addresses_APPEND"]
theorem heapAddresses_append {α β : Type} (xs ys : List (HeapElement α β)) (n : Nat) :
    heapAddresses n (xs ++ ys) =
      (fun address => heapAddresses n xs address ∨ heapAddresses (n + heapLength xs) ys address) := by
  induction xs generalizing n with
  | nil => simp [heapAddresses, heapLength]
  | cons head tail ih =>
    funext address
    simp only [List.cons_append, heapAddresses, ih, heapLength, List.map_cons, List.sum_cons]
    simp [Nat.add_assoc, or_assoc]

/-- Every element address is strictly below the end of its heap. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_addresses_LESS_heap_length"]
theorem heapAddresses_less_heapLength {α β : Type} (heap : List (HeapElement α β)) (n k : Nat)
    (member : heapAddresses n heap k) : k < n + heapLength heap := by
  induction heap generalizing n with
  | nil => simp [heapAddresses] at member
  | cons head tail ih =>
    simp only [heapAddresses] at member
    simp only [heapLength, List.map_cons, List.sum_cons]
    rcases member with rfl | member
    · have positive : 0 < elLength head := by cases head <;> simp [elLength]
      omega
    · have bound := ih (n + elLength head) member
      simp only [heapLength] at bound
      omega

/-- Every heap element address is at or above the heap's base address. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_addresses_LESS"]
theorem heapAddresses_base_le {α β : Type} (heap : List (HeapElement α β)) (n k : Nat)
    (member : heapAddresses n heap k) : n ≤ k := by
  induction heap generalizing n with
  | nil => simp [heapAddresses] at member
  | cons head tail ih =>
    simp only [heapAddresses] at member
    rcases member with rfl | member
    · exact Nat.le_refl _
    · have bound := ih (n + elLength head) member
      omega

/-- Every heap member is found by lookup at some element boundary. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "MEM_IMP_heap_lookup"]
theorem mem_imp_heapLookup {α β : Type} (xs : List (HeapElement α β)) (x : HeapElement α β)
    (member : x ∈ xs) : ∃ j, heapLookup j xs = some x := by
  induction xs with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨0, by simp [heapLookup]⟩
    · obtain ⟨j, found⟩ := ih member
      have positive : 0 < elLength head := by cases head <;> simp [elLength]
      refine ⟨j + elLength head, ?_⟩
      have nonzero : j + elLength head ≠ 0 := by omega
      have notInside : ¬ j + elLength head < elLength head := by omega
      simp only [heapLookup, nonzero, ite_false, notInside, Nat.add_sub_cancel]
      exact found

end Flapjack.Compiler.Backend
