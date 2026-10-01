import Flapjack.Compiler.Backend.RegAlloc.TagColour
import Flapjack.Compiler.Backend.RegAlloc.MoveTable
import Flapjack.RiscV.CakeRegAlloc

namespace Flapjack.Test.RegAllocMoveTableParity
open Flapjack Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc
/-! Same-input kernel replay of fresh original EVAL results
(`scripts/hol-probes/reg_alloc_move_table_probe.out`) for `tag_col`,
`extract_tag`, `unbound_colour` (including duplicate and unsorted inputs),
`pri_move_insert`, `undir_move_insert`, `moves_to_sp` and `resort_moves`
(raw sparse trees, independent Bool payloads, equal priorities). Finite
observations do not establish general cross-prover equivalence. -/

-- tc_fixed=5 / tc_atemp=0 / tc_stemp=0
example : tagCol (.Fixed 5) = 5 := by decide +kernel
example : tagCol .Atemp = 0 := by decide +kernel
example : tagCol .Stemp = 0 := by decide +kernel
-- et_fixed=18446744073709551616 / et_atemp=0 / et_stemp=0
example : extractTag (.Fixed 18446744073709551616) = 18446744073709551616 := by decide +kernel
example : extractTag .Atemp = 0 := by decide +kernel
example : extractTag .Stemp = 0 := by decide +kernel
-- uc_empty=4
example : unboundColour 4 [] = 4 := by decide +kernel
-- uc_gap=5
example : unboundColour 3 [0, 1, 3, 4, 7] = 5 := by decide +kernel
-- uc_below=2
example : unboundColour 2 [5] = 2 := by decide +kernel
-- uc_dup=3
example : unboundColour 1 [1, 1, 2] = 3 := by decide +kernel
-- uc_run=4
example : unboundColour 0 [0, 1, 2, 3] = 4 := by decide +kernel
-- uc_unsorted=2
example : unboundColour 2 [5, 2, 3] = 2 := by decide +kernel
-- uc_unsorted_miss=4
example : unboundColour 2 [2, 0, 3, 2] = 4 := by decide +kernel
-- uc_large=18446744073709551617
example : unboundColour 18446744073709551616 [18446744073709551616, 18446744073709551618] =
    18446744073709551617 := by decide +kernel
-- pmi_empty=BN LN (BN LN (LS [(7,9)]))
example : priMoveInsert (7 : Nat) 3 (9 : Nat) .ln = .bn .ln (.bn .ln (.ls [(7, 9)])) := by decide +kernel
-- pmi_existing=BS LN [] (BN LN (LS [(7,9); (1,2)]))
example : priMoveInsert (7 : Nat) 3 (9 : Nat) (sptInsert 3 [(1, 2)] (sptInsert 0 [] .ln)) =
    .bs .ln [] (.bn .ln (.ls [(7, 9), (1, 2)])) := by decide +kernel
-- pmi_bool=LS [(T,F); (F,T)]
example : priMoveInsert true 0 false (sptInsert 0 [(false, true)] .ln) =
    .ls [(true, false), (false, true)] := by decide +kernel
-- umi_empty=BN (LS [(7,1)]) (LS [(7,2)])
example : undirMoveInsert (7 : Nat) 1 2 .ln = .bn (.ls [(7, 1)]) (.ls [(7, 2)]) := by decide +kernel
-- umi_self=BN (BN LN (LS [(7,4); (7,4)])) LN
example : undirMoveInsert (7 : Nat) 4 4 .ln = .bn (.bn .ln (.ls [(7, 4), (7, 4)])) .ln := by decide +kernel
-- mts_empty=BN LN (BN (LS [(1,1)]) LN)
example : movesToSp ([] : List (Nat × (Nat × Nat))) (sptInsert 5 [(1, 1)] .ln) =
    .bn .ln (.bn (.ls [(1, 1)]) .ln) := by decide +kernel
-- mts_three=BN (LS [(5,1); (3,3); (5,1)]) (BS LN [(5,2); (5,2)] (LS [(3,2)]))
example : movesToSp [((5 : Nat), (1, 2)), (3, (2, 3)), (5, (1, 2))] .ln =
    .bn (.ls [(5, 1), (3, 3), (5, 1)]) (.bs .ln [(5, 2), (5, 2)] (.ls [(3, 2)])) := by decide +kernel
-- mts_bool=BS LN [(F,1); (T,1)] (LS [(F,0); (T,0)])
example : movesToSp [(true, (0, 1)), (false, (1, 0))] .ln =
    .bs .ln [(false, 1), (true, 1)] (.ls [(false, 0), (true, 0)]) := by decide +kernel
-- rm_three=BN (LS [1; 1; 3]) (BS LN [2; 2] (LS [2]))
example : resortMoves (movesToSp [((5 : Nat), (1, 2)), (3, (2, 3)), (5, (1, 2))] .ln) =
    .bn (.ls [1, 1, 3]) (.bs .ln [2, 2] (.ls [2])) := by decide +kernel
-- rm_ties=LS [F; F; T; T]
example : resortMoves (sptInsert 0 [(2, true), (2, false), (9, false), (0, true)] .ln) =
    .ls [false, false, true, true] := by decide +kernel
-- rm_empty_list=BN LN (LS [])
example : resortMoves (sptInsert 1 ([] : List (Nat × Nat)) .ln) = .bn .ln (.ls []) := by decide +kernel

/-- The executed allocator's `unbound_colour` is the reviewed definition. -/
example (col : Nat) (xs : List Nat) : cakeUnboundColour col xs = unboundColour col xs := rfl

end Flapjack.Test.RegAllocMoveTableParity
