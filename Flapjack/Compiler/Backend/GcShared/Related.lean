import Flapjack.Compiler.Backend.GcShared.HeapMap.Properties
import Flapjack.Misc.FiniteMapApply

/-! The abstract relation between a heap and its collected image. -/
namespace Flapjack.Compiler.Backend
open Flapjack

/-- Lookup-and-support view used to witness the finite-map representation. -/
structure GcMapBroad where
  lookup : Nat → Option Nat
  finiteSupport : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys

namespace GcMapBroad
def toBroad (map : HolFiniteMapExact Nat Nat) : GcMapBroad := ⟨map.lookup, map.finiteSupport⟩
def ofBroad (map : GcMapBroad) : HolFiniteMapExact Nat Nat := ⟨map.lookup, map.finiteSupport⟩
end GcMapBroad

/-- The canonical map's lookup and support survive the representation codec. -/
theorem holFmapAsFiniteSupportParamWitness_gcRelated_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    GcMapBroad.ofBroad (GcMapBroad.toBroad f) = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

/-- The finite address map injects old data locations into the new heap and
maps each data element and its outgoing pointers consistently. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "gc_related_def"
  (fmap_as_finite_support_parameters := [f])]
def gcRelated {α β : Type} (f : HolFiniteMapExact Nat Nat)
    (heap1 heap2 : List (HeapElement α β)) : Prop :=
  (∀ i, f.lookup i ≠ none → isSomeDataElement (heapLookup (holFapply f i) heap2)) ∧
  (∀ i j, f.lookup i ≠ none → f.lookup j ≠ none → holFapply f i = holFapply f j → i = j) ∧
  (∀ i, f.lookup i ≠ none → isSomeDataElement (heapLookup i heap1)) ∧
  ∀ i xs len payload, f.lookup i ≠ none → heapLookup i heap1 = some (.dataElement xs len payload) →
    heapLookup (holFapply f i) heap2 = some (.dataElement (addrMap (holFapply f) xs) len payload) ∧
    ∀ ptr value, .pointer ptr value ∈ xs → f.lookup ptr ≠ none

end Flapjack.Compiler.Backend
