import Flapjack.Misc.Sorting

namespace Flapjack.Test.HolSortingParity
open Flapjack
/-! Kernel replay of fresh original HOL `SORTED`/`PART`/`PARTITION` results
(`scripts/hol-probes/hol_sorting_probe.out`) at the pinned HOL revision,
including a non-transitive relation for `SORTED`. Finite observations do not
establish cross-prover equivalence. -/

-- sorted_empty=T
example : holSorted (fun x y : Nat => x < y) [] := by simp [holSorted]
-- sorted_single=T
example : holSorted (fun x y : Nat => x < y) [5] := by simp [holSorted]
-- sorted_asc=T
example : holSorted (fun x y : Nat => x < y) [1, 2, 5] := by simp [holSorted]
-- sorted_dup=F
example : ¬ holSorted (fun x y : Nat => x < y) [1, 2, 2] := by simp [holSorted]
-- sorted_le_dup=T
example : holSorted (fun x y : Nat => x ≤ y) [1, 2, 2] := by simp [holSorted]
-- sorted_gt=T
example : holSorted (fun x y : Nat => x > y) [9, 4, 1, 0] := by simp [holSorted]
-- sorted_nontrans=T
example : holSorted (fun x y : Nat => x ≠ y) [1, 2, 1] := by simp [holSorted]
-- part_basic=([2; 1; 10],[7; 5; 20])
example : holPart (fun x : Nat => decide (x < 3)) [1, 5, 2, 7] [10] [20] = ([2, 1, 10], [7, 5, 20]) := by
  decide +kernel
-- part_empty=([1],[2])
example : holPart (fun _ : Nat => true) [] [1] [2] = ([1], [2]) := by decide +kernel
-- partition_basic=([6; 4; 2],[3; 1])
example : holPartition (fun x : Nat => decide (x % 2 = 0)) [1, 2, 3, 4, 6] = ([6, 4, 2], [3, 1]) := by
  decide +kernel
-- partition_bool=([T; T],[F])
example : holPartition (fun b : Bool => b) [true, false, true] = ([true, true], [false]) := by
  decide +kernel

end Flapjack.Test.HolSortingParity
