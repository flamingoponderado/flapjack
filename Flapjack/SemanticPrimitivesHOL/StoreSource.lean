module

public import Flapjack.SemanticPrimitivesHOL

@[expose] public section

/-! Guarded source equations for the shared source and flat stores. -/
namespace Flapjack.SemanticPrimitivesHOL

/-- Store lookup uses the original list bound before reading the element. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_lookup_def"]
theorem storeLookup_source {α : Type} (n : Nat) (store : Store α) :
    storeLookup n store = if h : n < store.length then some store[n] else none := by
  by_cases h : n < store.length <;> simp [storeLookup, h]

/-- Store assignment requires an in-range slot of a compatible store type. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_assign_def"]
theorem storeAssign_source {α : Type} (n : Nat) (value : StoreValue α) (store : Store α) :
    storeAssign n value store =
      if h : n < store.length then
        if storeValueSameType store[n] value then some (store.set n value) else none
      else none := by
  by_cases h : n < store.length <;> simp [storeAssign, h]

end Flapjack.SemanticPrimitivesHOL
