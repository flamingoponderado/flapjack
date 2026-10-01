import Flapjack.Compiler.Backend.WordAlloc.HeuCall

namespace Flapjack.Test.HeuCallParity
open Flapjack Flapjack.WordAlloc
/-! Kernel exact-tree replay of original call-name unions. Generic payload
types and malformed nodes are retained where the source retains them. Finite
observations do not establish cross-prover equivalence or allocator routing. -/
-- hc_merge_empty=T
example : heuMergeCall .ln .ln = .ln := by decide +kernel
-- hc_merge_left=T
example : heuMergeCall (sptInsert 1 () .ln) .ln = sptInsert 1 () .ln := by decide +kernel
-- hc_merge_right=T
example : heuMergeCall .ln (sptInsert 2 () .ln) = sptInsert 2 () .ln := by decide +kernel
-- hc_merge_overlap=T
example : heuMergeCall (sptInsert 1 () .ln) (sptInsert 1 () .ln) =
    sptInsert 1 () .ln := by decide +kernel
-- hc_merge_disjoint=T
example : heuMergeCall (sptInsert 1 () .ln) (sptInsert 2 () .ln) =
    sptInsert 1 () (sptInsert 2 () .ln) := by decide +kernel
-- hc_merge_raw_left=T
example : heuMergeCall (.bn .ln .ln) .ln = .bn .ln .ln := by decide +kernel
-- hc_merge_raw_right=T
example : heuMergeCall .ln (.bn .ln .ln) = .bn .ln .ln := by decide +kernel
-- hc_merge_raw_root=T
example : heuMergeCall (.bn .ln .ln) (.ls ()) = .bs .ln () .ln := by decide +kernel
-- hc_add_empty=T
example : addCall (.ln : Spt Nat) (sptInsert 3 () .ln) =
    sptInsert 3 () .ln := by decide +kernel
-- hc_add_nat=T
example : addCall (sptInsert 1 18446744073709551616 .ln) .ln =
    sptInsert 1 () .ln := by decide +kernel
-- hc_add_bool=T
example : addCall (sptInsert 2 false .ln) (sptInsert 1 () .ln) =
    sptInsert 1 () (sptInsert 2 () .ln) := by decide +kernel
-- hc_add_tuple=T
example : addCall (sptInsert 5 ((2 : Nat),3,5,7,11) .ln) (sptInsert 5 () .ln) =
    sptInsert 5 () .ln := by decide +kernel
-- hc_add_nested=T
example : addCall (sptInsert 1 false (sptInsert 5 true (sptInsert 6 false .ln)))
    (sptInsert 2 () (sptInsert 6 () .ln)) =
    sptInsert 1 () (sptInsert 2 () (sptInsert 5 () (sptInsert 6 () .ln))) := by decide +kernel
-- hc_add_raw_bn=T
example : addCall (.bn .ln .ln : Spt Nat) .ln = .bn .ln .ln := by decide +kernel
-- hc_add_raw_bs=T
example : addCall (.bs .ln false .ln) .ln = .bs .ln () .ln := by decide +kernel
-- hc_add_raw_overlap=T
example : addCall (.bs .ln false .ln) (.ls ()) = .bs .ln () .ln := by decide +kernel
end Flapjack.Test.HeuCallParity
