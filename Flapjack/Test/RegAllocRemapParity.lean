import Flapjack.Compiler.Backend.RegAlloc.Remap

namespace Flapjack.Test.RegAllocRemapParity
open Flapjack Flapjack.RegAlloc
/-! Exact-tree kernel replay of fresh original remapping observations. These
fixtures exercise source traversal order; they do not establish a general
cross-prover equivalence or completion of the production allocator route. -/
-- remap_empty=T
example : mkBij (.delta [] []) = (.ln,.ln,0) := by decide +kernel
-- remap_delta=T
example : mkBij (.delta [7,3] [5,7]) = ((sptInsert 3 2 (sptInsert 7 1 (sptInsert 5 0 .ln))),(sptInsert 2 3 (sptInsert 1 7 (sptInsert 0 5 .ln))),3) := by decide +kernel
-- remap_duplicate=T
example : mkBij (.delta [7,7] [7,7]) = ((sptInsert 7 0 .ln),(sptInsert 0 7 .ln),1) := by decide +kernel
-- remap_seq=T
example : mkBij (.seq (.delta [1] []) (.delta [2] [])) = ((sptInsert 1 1 (sptInsert 2 0 .ln)),(sptInsert 1 1 (sptInsert 0 2 .ln)),2) := by decide +kernel
-- remap_branch=T
example : mkBij (.branch none (.delta [1] []) (.delta [2] [])) = ((sptInsert 2 1 (sptInsert 1 0 .ln)),(sptInsert 1 2 (sptInsert 0 1 .ln)),2) := by decide +kernel
-- remap_fixed=T
example : mkBij (.branch (some (.ls ())) (.delta [1] []) (.delta [2] [])) = ((sptInsert 0 2 (sptInsert 2 1 (sptInsert 1 0 .ln))),(sptInsert 2 0 (sptInsert 1 2 (sptInsert 0 1 .ln))),3) := by decide +kernel
-- remap_raw_empty=T
example : mkBij (.set (.bn .ln .ln)) = (.ln,.ln,0) := by decide +kernel
-- remap_raw_root=T
example : mkBij (.set (.bs .ln () .ln)) = ((sptInsert 0 0 .ln),(sptInsert 0 0 .ln),1) := by decide +kernel
-- remap_set_order=T
example : mkBij (.set (.bs (.ls ()) () (.ls ()))) = ((sptInsert 2 2 (sptInsert 0 1 (sptInsert 1 0 .ln))),(sptInsert 2 2 (sptInsert 1 0 (sptInsert 0 1 .ln))),3) := by decide +kernel
-- remap_large=T
example : mkBij (.delta [18446744073709551616] []) = ((sptInsert 18446744073709551616 0 .ln),(sptInsert 0 18446744073709551616 .ln),1) := by decide +kernel
-- remap_nested=T
example : mkBij (.seq (.branch none (.delta [1] []) (.delta [2] [])) (.delta [3,1] [])) = ((sptInsert 2 2 (sptInsert 1 1 (sptInsert 3 0 .ln))),(sptInsert 2 2 (sptInsert 1 1 (sptInsert 0 3 .ln))),3) := by decide +kernel
-- remap_initial=T
example : listRemap [7,8,7] (sptInsert 7 99 .ln, .ln, 18446744073709551616) =
    (sptInsert 8 18446744073709551616 (sptInsert 7 99 .ln),
      sptInsert 18446744073709551616 8 .ln, 18446744073709551617) := by decide +kernel

end Flapjack.Test.RegAllocRemapParity
