import Flapjack.Misc.Mergesort

namespace Flapjack.Test.HolMergesortParity
open Flapjack.Mergesort
/-! Kernel replay of fresh original HOL `sort2`/`sort3`/`merge`/`mergesortN` results
(`scripts/hol-probes/hol_mergesort_probe.out`) at the pinned HOL revision, including a
non-strict, a strict and a non-total relation and counts that differ from the list
length. A HOL relation `R : num -> num -> bool` is the Lean `Bool` relation. Finite
observations do not establish cross-prover equivalence. -/

private def lt (x y : Nat) : Bool := decide (x < y)
private def le (x y : Nat) : Bool := decide (x ≤ y)
private def evenL (x _ : Nat) : Bool := decide (x % 2 = 0)

-- sort2_lt=[3; 5]
example : sort2 lt 5 3 = [3, 5] := by decide +kernel
-- sort2_eq_le=[4; 4]
example : sort2 le 4 4 = [4, 4] := by decide +kernel
-- sort3_all=[[1; 2; 3]; [1; 2; 3]; [1; 2; 3]; [1; 2; 3]; [1; 2; 3]; [1; 2; 3]]
example : [(1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1)].map
    (fun (p : Nat × Nat × Nat) => sort3 lt p.1 p.2.1 p.2.2) =
    [[1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3], [1, 2, 3]] := by decide +kernel
-- sort3_dup_le=[1; 2; 2]
example : sort3 le 2 1 2 = [1, 2, 2] := by decide +kernel
-- merge_basic=[1; 2; 4; 4; 5; 6]
example : merge le [1, 4, 6] [2, 4, 5] = [1, 2, 4, 4, 5, 6] := by decide +kernel
-- merge_unsorted=[3; 2; 5; 1]
example : merge lt [5, 1] [3, 2] = [3, 2, 5, 1] := by decide +kernel
-- merge_left_empty=[3; 2]
example : merge lt [] [3, 2] = [3, 2] := by decide +kernel
-- merge_nontotal=[4; 5; 1; 2; 3]
example : merge evenL [1, 2, 3] [4, 5] = [4, 5, 1, 2, 3] := by decide +kernel
-- msn_full=[1; 2; 3; 3; 5; 8; 9]
example : mergesortN le 7 [5, 3, 8, 1, 9, 2, 3] = [1, 2, 3, 3, 5, 8, 9] := by decide +kernel
-- msn_prefix=[1; 3; 5; 8]
example : mergesortN lt 4 [5, 3, 8, 1, 9, 2] = [1, 3, 5, 8] := by decide +kernel
-- msn_over=[1; 3; 4]
example : mergesortN lt 6 [4, 1, 3] = [1, 3, 4] := by decide +kernel
-- msn_three_short=[2; 9]
example : mergesortN lt 3 [9, 2] = [2, 9] := by decide +kernel
-- msn_nontotal=[2; 4; 5; 3; 1]
example : mergesortN evenL 5 [1, 2, 3, 4, 5] = [2, 4, 5, 3, 1] := by decide +kernel
-- msn_zero=[]
example : mergesortN lt 0 [1, 2] = [] := by decide +kernel

end Flapjack.Test.HolMergesortParity
