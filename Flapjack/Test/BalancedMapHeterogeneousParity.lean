import Flapjack.Misc.BalancedMap.Domain
import Flapjack.Misc.BalancedMap.KeySetComparison

namespace Flapjack.Test.BalancedMapHeterogeneousParity
open Flapjack Flapjack.Misc.BalancedMap

example {κ ι ν : Type} (cmp : κ → ι → Ordering) (tree : Map κ ν) (query : Set ι) :
    (toFmap cmp tree).lookup query = semanticLookup cmp tree query :=
  holFmapAsFiniteSupportResultWitness_toFmap cmp tree query

example {κ ι ν : Type} (cmp : κ → ι → Ordering) (tree : Map κ ν) (query : Set ι)
    (h : (toFmap cmp tree).lookup query ≠ none) : ∃ key : κ, query = keySet cmp key :=
  toFmapKeySet cmp query tree h

private def hetero (key : Bool) (query : Nat) : Ordering :=
  if key && query == 0 then .eq else .gt

example : keySet hetero true = {query : Nat | hetero true query = .eq} := rfl
example : (toFmap hetero (.bin 0 true 99 .tip .tip)).lookup (keySet hetero true) = some 99 := by
  classical
  simp [toFmap, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

example {κ ι ρ : Type} (cmp : κ → ι → ρ) (key : κ) (keys : Set ι) (result : ρ) :
    keySetCmp cmp key keys result ↔ ∀ query, query ∈ keys → cmp key query = result := Iff.rfl
example {κ ι ρ : Type} (cmp : κ → ι → ρ) (left : Set κ) (right : Set ι) (result : ρ) :
    keySetCmp2 cmp left right result ↔
      ∀ k1 k2, k1 ∈ left ∧ k2 ∈ right → cmp k1 k2 = result := Iff.rfl
example : keySetCmp (fun (_ : Bool) (_ : Nat) => "value") true Set.univ "value" := by
  intro query h; rfl
example : keySetCmp2 (fun (_ : Bool) (_ : Nat) => "value") Set.univ Set.univ "value" := by
  intro k1 k2 h; rfl

-- Recursive core uses independent query/key types, including malformed sizes.
example : lookup hetero true (.bin 0 0 "root" .tip .tip) = some "root" := rfl
example : member hetero true (.bin 0 0 "root" .tip .tip) = true := rfl
example : lookup (fun (_ : Bool) (_ : Nat) => .lt) false
    (.bin 0 1 "root" (.bin 99 2 "left" .tip .tip) .tip) = none := rfl
example : member (fun (_ : Bool) (_ : Nat) => .gt) false
    (.bin 0 1 "root" .tip (.bin 99 2 "right" .tip .tip)) = false := rfl
example {ι κ ν : Type} (cmp : ι → κ → Ordering) (query : ι) :
    lookup cmp query (.tip : Map κ ν) = none := rfl
example {ι κ ν : Type} (cmp : ι → κ → Ordering) (query : ι) :
    member cmp query (.tip : Map κ ν) = false := rfl

end Flapjack.Test.BalancedMapHeterogeneousParity
