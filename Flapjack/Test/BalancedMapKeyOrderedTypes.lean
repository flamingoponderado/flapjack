import Flapjack.Misc.BalancedMap.Invariants

namespace Flapjack.Test.BalancedMapKeyOrderedTypes
open Flapjack.Misc.BalancedMap

example {ι κ ρ ν : Type} (cmp : ι → κ → ρ) (key : ι) (result : ρ) :
    keyOrdered cmp key (.tip : Map κ ν) result := trivial
example {ι κ ρ ν : Type} (cmp : ι → κ → ρ) (key : ι) (result : ρ)
    (size : Nat) (stored : κ) (value : ν) (left right : Map κ ν) :
    keyOrdered cmp key (.bin size stored value left right) result ↔
      cmp key stored = result ∧ keyOrdered cmp key left result ∧
        keyOrdered cmp key right result := Iff.rfl
example : keyOrdered (fun (_ : Bool) (_ : Nat) => "value") true
    (.bin 0 1 false (.bin 99 2 true .tip .tip) .tip) "value" := by
  simp [keyOrdered]
example : ¬ keyOrdered (fun (_ : Bool) (_ : Nat) => "value") false
    (.bin 0 1 false .tip (.bin 99 2 true .tip .tip)) "other" := by
  simp [keyOrdered]

end Flapjack.Test.BalancedMapKeyOrderedTypes
