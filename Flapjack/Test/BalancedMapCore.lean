import Flapjack.Misc.BalancedMap.Core

namespace Flapjack.Test.BalancedMapCore
open Misc.BalancedMap

-- Flapjack-only regression fixtures: cached metadata and arbitrary comparator
-- results are observable even when the input is not a well-formed search tree.
private def malformed : Map Nat Nat :=
  .bin 0 10 100 (.bin 90 20 200 .tip .tip) (.bin 80 5 50 .tip .tip)

example : size malformed = 0 := rfl
example : size (bin 10 100 (.bin 90 20 200 .tip .tip)
    (.bin 80 5 50 .tip .tip)) = 171 := rfl
example : null malformed = false := rfl
example : null (empty : Map Nat Nat) = true := rfl
example : lookup (fun _ _ => .eq) 999 malformed = some 100 := rfl
example : lookup compare 20 malformed = none := by decide
example : lookup compare 10 malformed = some 100 := by decide
example : lookup compare 5 malformed = none := by decide
example : member (fun _ _ => .eq) 999 malformed = true := rfl
example : member compare 20 malformed = false := by decide
example : lookup compare 7 (singleton 7 70) = some 70 := by decide
example : lookup compare 8 (singleton 7 70) = none := by decide

-- Universal equations check both recursive branches without assuming good_cmp.
example {κ ν : Type} (cmp : κ → κ → Ordering) (key key' : κ)
    (value : ν) (n : Nat) (left right : Map κ ν) (h : cmp key key' = .lt) :
    lookup cmp key (.bin n key' value left right) = lookup cmp key left := by
  simp [lookup, h]

example {κ ν : Type} (cmp : κ → κ → Ordering) (key key' : κ)
    (value : ν) (n : Nat) (left right : Map κ ν) (h : cmp key key' = .gt) :
    lookup cmp key (.bin n key' value left right) = lookup cmp key right := by
  simp [lookup, h]

end Flapjack.Test.BalancedMapCore

def Flapjack.Test.BalancedMapCore.runChecks : IO Bool := do
  IO.println "BalancedMapCore: 14 kernel fixtures checked"
  return true
