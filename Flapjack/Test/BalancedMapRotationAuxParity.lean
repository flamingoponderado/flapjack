import Flapjack.Misc.BalancedMap.RotationAux

namespace Flapjack.Test.BalancedMapRotationAuxParity
open Flapjack.Misc.BalancedMap

example : singleR 2 20 (.bin 999 1 10 .tip .tip) .tip =
    (.bin 2 1 10 .tip (.bin 1 2 20 .tip .tip) : Map Nat Nat) := by
  rw [singleRDef]
  rfl
example : singleL 1 10 .tip (.bin 999 2 20 .tip .tip) =
    (.bin 2 2 20 (.bin 1 1 10 .tip .tip) .tip : Map Nat Nat) := by
  rw [singleLDef]
  rfl
example : doubleR 2 20 (.bin 999 0 0 .tip (.bin 888 1 10 .tip .tip)) .tip =
    (.bin 3 1 10 (.bin 1 0 0 .tip .tip) (.bin 1 2 20 .tip .tip) : Map Nat Nat) := by
  rw [doubleRDef]
  rfl
example : doubleL 0 0 .tip (.bin 999 2 20 (.bin 888 1 10 .tip .tip) .tip) =
    (.bin 3 1 10 (.bin 1 0 0 .tip .tip) (.bin 1 2 20 .tip .tip) : Map Nat Nat) := by
  rw [doubleLDef]
  rfl

/-- Missing-case outputs remain unspecified, but the original rotate-to-double
equations themselves hold for all independent key/payload carriers. -/
example {κ ν : Type} (k : κ) (v : ν) (left : Map κ ν) :
    rotateL k v left .tip = doubleL k v left .tip := rfl
example {κ ν : Type} (k : κ) (v : ν) (right : Map κ ν) :
    rotateR k v .tip right = doubleR k v .tip right := rfl

example : rotateR 2 20 (.bin 999 1 10 (.bin 1 0 0 .tip .tip) .tip) .tip =
    (.bin 3 1 10 (.bin 1 0 0 .tip .tip) (.bin 1 2 20 .tip .tip) : Map Nat Nat) := by
  change singleR 2 20 (.bin 999 1 10 (.bin 1 0 0 .tip .tip) .tip) .tip = _
  rw [singleRDef]
  rfl
example : rotateL 0 0 .tip (.bin 999 1 10 .tip (.bin 1 2 20 .tip .tip)) =
    (.bin 3 1 10 (.bin 1 0 0 .tip .tip) (.bin 1 2 20 .tip .tip) : Map Nat Nat) := by
  change singleL 0 0 .tip (.bin 999 1 10 .tip (.bin 1 2 20 .tip .tip)) = _
  rw [singleLDef]
  rfl
example : bal 1 10 .tip .tip = (.bin 1 1 10 .tip .tip : Map Nat Nat) := rfl
example : balL 1 10 .tip .tip = (.bin 1 1 10 .tip .tip : Map Nat Nat) := rfl
example : balR 1 10 .tip .tip = (.bin 1 1 10 .tip .tip : Map Nat Nat) := rfl

example : rotateR 2 20 (.bin 999 0 0 .tip (.bin 888 1 10 .tip .tip)) .tip =
    (.bin 3 1 10 (.bin 1 0 0 .tip .tip) (.bin 1 2 20 .tip .tip) : Map Nat Nat) := by
  change doubleR 2 20 (.bin 999 0 0 .tip (.bin 888 1 10 .tip .tip)) .tip = _
  rw [doubleRDef]
  rfl
example : rotateL 0 0 .tip (.bin 999 2 20 (.bin 888 1 10 .tip .tip) .tip) =
    (.bin 3 1 10 (.bin 1 0 0 .tip .tip) (.bin 1 2 20 .tip .tip) : Map Nat Nat) := by
  change doubleL 0 0 .tip (.bin 999 2 20 (.bin 888 1 10 .tip .tip) .tip) = _
  rw [doubleLDef]
  rfl

end Flapjack.Test.BalancedMapRotationAuxParity
