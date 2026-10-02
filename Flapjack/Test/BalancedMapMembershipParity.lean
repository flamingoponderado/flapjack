import Flapjack.Misc.BalancedMap.Membership

namespace Flapjack.Test.BalancedMapMembershipParity
open Flapjack.Misc.BalancedMap

example {ι κ ν : Type} (cmp : ι → κ → Ordering) (query : ι) (tree : Map κ ν) :
    member cmp query tree = (lookup cmp query tree).isSome :=
  memberEqLookup cmp query tree

example : member (fun (_ : Bool) (_ : Nat) => .eq) true (.tip : Map Nat Nat) = false := rfl
example : member (fun (_ : Bool) (_ : Nat) => .eq) false
    (.bin 0 7 99 .tip .tip) = true := rfl
example : member (fun (_ : Bool) (_ : Nat) => .lt) false
    (.bin 0 7 99 .tip .tip) = false := rfl
example : member (fun (_ : Bool) (_ : Nat) => .gt) false
    (.bin 0 7 99 .tip .tip) = false := rfl
example : member (fun (_ : Bool) (k : Nat) => if k = 7 then .lt else .eq) true
    (.bin 0 7 99 (.bin 999 8 22 .tip .tip) .tip) = true := rfl
example : member (fun (_ : Bool) (k : Nat) => if k = 7 then .gt else .eq) false
    (.bin 0 7 99 .tip (.bin 999 8 22 .tip .tip)) = true := rfl

end Flapjack.Test.BalancedMapMembershipParity
