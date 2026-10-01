import Flapjack.Misc.LookupAny
import Flapjack.Misc.Sptree
import Flapjack.Misc.FindIndex

/-! Kernel replay of the direct original-HOL `EVAL` rows in
`scripts/hol-probes/misc_lookup_any_find_index_probe.out` for the misc
prerequisites `lookup_any_def` and `find_index_def`
(bead `flapjack-pxn.18.5.15.10.10`). -/

namespace Flapjack.Test.MiscLookupAnyFindIndexParity

open Flapjack
open Flapjack.Misc

example : lookupAny 2 (sptFromList2 [10, 20, 30]) 99 = 20 := by decide +kernel
example : lookupAny 0 (sptFromList2 [10, 20, 30]) 99 = 10 := by decide +kernel
example : lookupAny 1 (sptFromList2 [10, 20, 30]) 99 = 99 := by decide +kernel
example : lookupAny 0 (sptFromList2 ([] : List Nat)) 7 = 7 := by decide +kernel

example : findIndex 0 ([0, 0] : List Nat) 0 = some 0 := rfl
example : findIndex 2 ([1, 2, 3] : List Nat) 7 = some 8 := rfl
example : findIndex 2 ([1, 3] : List Nat) 7 = none := rfl
example : findIndex 2 ([1, 2, 2] : List Nat) 3 = some 4 := rfl

def runChecks : IO Bool := do
  IO.println "PASS misc lookup_any/find_index match all 8 oracle rows"
  pure true

end Flapjack.Test.MiscLookupAnyFindIndexParity
