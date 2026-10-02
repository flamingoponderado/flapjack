import Flapjack.Misc.BalancedMap.NullSemantics
namespace Flapjack.Test.BalancedMapNullParity
open Flapjack Flapjack.Misc.BalancedMap
example {κ ι ν : Type} (cmp : κ → ι → Ordering) (tree : Map κ ν) :
    null tree = true ↔ toFmap cmp tree = HolFiniteMapExact.empty := nullThm cmp tree
example : null (.tip : Map Nat Nat) = true := rfl
example : null (.bin 0 1 99 .tip .tip : Map Nat Nat) = false := rfl
example : toFmap (fun (_ : Bool) (_ : Nat) => .eq)
    (.tip : Map Bool String) = HolFiniteMapExact.empty := rfl
example : toFmap (fun (_ : Bool) (_ : Nat) => .eq)
    (.bin 0 true "root" .tip .tip) ≠ HolFiniteMapExact.empty := by
  intro h
  have impossible := (nullThm (fun (_ : Bool) (_ : Nat) => .eq)
    (.bin 0 true "root" .tip .tip)).mpr h
  cases impossible
end Flapjack.Test.BalancedMapNullParity
