import Flapjack.Compiler.Backend.WordAlloc.HeuMax

namespace Flapjack.Test.HeuMaxParity
open Flapjack Flapjack.WordAlloc
/-! Exact-tree kernel replay of direct original HOL branch joins, including
raw-tree orientation and indexed key order. Finite observations do not establish
cross-prover equivalence or executed allocator routing. -/
-- hm_tuple=T
example : heuMax (1,8,3,10,5) (6,2,9,4,7) = (6,8,9,10,7) := by decide +kernel
-- hm_tuple_equal=T
example : heuMax (4,4,4,4,4) (4,4,4,4,4) = (4,4,4,4,4) := by decide +kernel
-- hm_tuple_zero=T
example : heuMax (0,0,0,0,0) (6,2,9,4,7) = (6,2,9,4,7) := by decide +kernel
-- hm_tuple_large=T
example : heuMax (18446744073709551616,0,2,0,4) (0,18446744073709551617,0,3,0) = (18446744073709551616,18446744073709551617,2,3,4) := by decide +kernel
-- hm_empty=T
example : heuMaxAll .ln .ln = .ln := by decide +kernel
-- hm_left=T
example : heuMaxAll (sptInsert 4 (1,8,3,10,5) .ln) .ln = (sptInsert 4 (1,8,3,10,5) .ln) := by decide +kernel
-- hm_right=T
example : heuMaxAll .ln (sptInsert 5 (6,2,9,4,7) .ln) = (sptInsert 5 (6,2,9,4,7) .ln) := by decide +kernel
-- hm_overlap=T
example : heuMaxAll (sptInsert 1 (1,8,3,10,5) .ln) (sptInsert 1 (6,2,9,4,7) .ln) = (sptInsert 1 (6,8,9,10,7) .ln) := by decide +kernel
-- hm_disjoint=T
example : heuMaxAll (sptInsert 1 (1,8,3,10,5) .ln) (sptInsert 2 (6,2,9,4,7) .ln) = (sptInsert 1 (1,8,3,10,5) (sptInsert 2 (6,2,9,4,7) .ln)) := by decide +kernel
-- hm_mixed=T
example : heuMaxAll (sptInsert 0 (1,8,3,10,5) (sptInsert 1 (6,2,9,4,7) .ln)) (sptInsert 1 (4,4,4,4,4) (sptInsert 2 (6,2,9,4,7) .ln)) = (sptInsert 0 (1,8,3,10,5) (sptInsert 1 (6,4,9,4,7) (sptInsert 2 (6,2,9,4,7) .ln))) := by decide +kernel
-- hm_nested=T
example : heuMaxAll (sptInsert 1 (1,8,3,10,5) (sptInsert 2 (6,2,9,4,7) (sptInsert 5 (4,4,4,4,4) (sptInsert 6 (7,7,7,7,7) .ln)))) (sptInsert 1 (7,7,7,7,7) (sptInsert 2 (4,4,4,4,4) (sptInsert 3 (6,2,9,4,7) .ln))) = (sptInsert 1 (7,8,7,10,7) (sptInsert 2 (6,4,9,4,7) (sptInsert 3 (6,2,9,4,7) (sptInsert 5 (4,4,4,4,4) (sptInsert 6 (7,7,7,7,7) .ln))))) := by decide +kernel
-- hm_raw_left_bn=T
example : heuMaxAll (.bn .ln .ln) .ln = (.bn .ln .ln) := by decide +kernel
-- hm_raw_right_bn=T
example : heuMaxAll .ln (.bn .ln .ln) = .ln := by decide +kernel
-- hm_raw_both_bn=T
example : heuMaxAll (.bn .ln .ln) (.bn .ln .ln) = .ln := by decide +kernel
-- hm_raw_left_bs=T
example : heuMaxAll (.bs .ln (1,8,3,10,5) .ln) .ln = (.bs .ln (1,8,3,10,5) .ln) := by decide +kernel
-- hm_raw_right_bs=T
example : heuMaxAll .ln (.bs .ln (6,2,9,4,7) .ln) = (.ls (6,2,9,4,7)) := by decide +kernel
-- hm_raw_both_bs=T
example : heuMaxAll (.bs .ln (1,8,3,10,5) .ln) (.bs .ln (6,2,9,4,7) .ln) = (.ls (6,8,9,10,7)) := by decide +kernel
-- hm_raw_bs_leaf=T
example : heuMaxAll (.bs .ln (1,8,3,10,5) .ln) (.ls (6,2,9,4,7)) = (.bs .ln (6,8,9,10,7) .ln) := by decide +kernel
-- hm_raw_leaf_bs=T
example : heuMaxAll (.ls (1,8,3,10,5)) (.bs .ln (6,2,9,4,7) .ln) = (.ls (6,8,9,10,7)) := by decide +kernel
-- hm_raw_empty_leaf=T
example : heuMaxAll (.bn .ln .ln) (.ls (6,2,9,4,7)) = (.bs .ln (6,2,9,4,7) .ln) := by decide +kernel
end Flapjack.Test.HeuMaxParity
