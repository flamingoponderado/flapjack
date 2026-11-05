import Flapjack.Compiler.Backend.CopyingGc
import Flapjack.Compiler.Backend.GcShared.HeapSimilarity
import Flapjack.Compiler.Backend.GcShared.Reachability

/-! Abstract invariant for the copying collector. -/
namespace Flapjack.Compiler.Backend.CopyingGc

/-- The source-shaped copying collector invariant. This proof-side definition
uses the canonical finite map internally; it remains untagged until the
representation qualifier can record that internal use. -/
def gcInv {α β : Type}
    (h1 h2 : List (HeapElement α β)) (a n : Nat) (heap : List (HeapElement α β))
    (ok : Bool) (limit : Nat) (heap0 : List (HeapElement α β))
    (roots0 : List (HeapAddress α)) : Prop :=
  let f := heapMap 0 heap
  let target := heapAddresses 0 (h1 ++ h2)
  a + n = limit ∧ a = heapLength (h1 ++ h2) ∧
  n = heapLength (heap.filter (fun h => !(isForwardPointer h))) ∧ ok = true ∧
  heapLength heap = limit ∧ heapOk heap0 limit ∧ heapsSimilar heap0 heap ∧
  (∀ h ∈ h1, isDataElement h) ∧ (∀ h ∈ h2, isDataElement h) ∧
  (∀ i, f.lookup i ≠ none → target (heapMap1 heap i)) ∧
  (∀ i j, f.lookup i ≠ none → f.lookup j ≠ none → heapMap1 heap i = heapMap1 heap j → i = j) ∧
  (∀ j, target j → ∃ i, f.lookup i ≠ none ∧ heapMap1 heap i = j) ∧
  ∀ i j, f.lookup i = some j →
    ∃ xs len data, heapLookup i heap0 = some (.dataElement xs len data) ∧
      heapLookup j (h1 ++ h2) = some (.dataElement
        (if j < heapLength h1 then addrMap (heapMap1 heap) xs else xs) len data) ∧
      reachableAddresses roots0 heap0 i ∧
      ∀ ptr value, .pointer ptr value ∈ xs → j < heapLength h1 → f.lookup ptr ≠ none

/-- The empty initial copying state satisfies the invariant exactly when the
initial heap is well formed. This is a Flapjack proof about `gcInv`, which is
not yet tagged as the original HOL definition. -/
theorem gcInv_init {α β : Type} (heap : List (HeapElement α β))
    (roots : List (HeapAddress α)) (limit : Nat) :
    gcInv [] [] 0 limit heap true limit heap roots ↔ heapOk heap limit := by
  constructor
  · intro invariant
    exact invariant.2.2.2.2.2.1
  · intro good
    have noForward := good.2.1
    have emptyMap : ∀ key, (heapMap 0 heap).lookup key = none := by
      intro key
      have domainEq := congrFun (heapMap_empty heap 0 noForward) key
      by_cases lookup : (heapMap 0 heap).lookup key = none
      · exact lookup
      · exact False.elim (domainEq.mp lookup)
    have filtered := filter_notForward heap noForward
    have similar := heapsSimilar_refl heap noForward
    have lengthEq : (heap.map elLength).sum = limit := good.1
    simp [gcInv, heapAddresses, heapLength, filtered, similar, emptyMap, good, lengthEq]

end Flapjack.Compiler.Backend.CopyingGc
