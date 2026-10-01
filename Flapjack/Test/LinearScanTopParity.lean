import Flapjack.Compiler.Backend.LinearScan.TopLevel
namespace Flapjack.Test.LinearScanTopParity
open RegAlloc LinearScan Translator.Monadic.MonadBase
-- Full-value replay of the fourteen original linear_scan_top_probe rows, including six
-- end-to-end linear_scan_reg_alloc runs (raw sparse-tree constructors). Finite
-- observations only;
-- no allocator soundness or production routing is claimed.
-- bijection_seq
example : findBijectionClashTree findBijectionInit (.seq (.delta [5, 3] [2]) (.set (sptInsert 9 () (sptInsert 4 () .ln)))) =
    { bij := .bn (.bs .ln 2 (.ls 4)) (.bn (.bs .ln 1 (.ls 5)) (.ls 3)), invbij := .bn (.bs .ln 2 (.ls 4)) (.bs (.ls 9) 5 (.ls 3)), nmax := 5, nstack := 7, nalloc := 9 } := by decide +kernel
-- bijection_branch
example : findBijectionClashTree findBijectionInit (.branch (some (sptInsert 7 () .ln)) (.delta [1] [5]) (.delta [11] [0])) =
    { bij := .bs .ln 0 (.bs (.ls 1) 5 (.bn (.ls 3) (.ls 7))), invbij := .bs .ln 0 (.bs (.ls 1) 5 (.bs .ln 11 (.ls 7))), nmax := 7, nstack := 11, nalloc := 9 } := by decide +kernel
-- apply_bij_tree
example : applyBijOnClashTree (.branch (some (sptInsert 7 () .ln)) (.delta [1, 3] [5]) (.set (sptInsert 3 () .ln))) (sptInsert 1 9 (sptInsert 3 4 (sptInsert 7 2 .ln))) =
    .branch (some (.bn (.ls ()) .ln)) (.delta [9, 4] [0]) (.set (.bn (.bn .ln (.ls ())) .ln)) := by decide +kernel
-- apply_bijection
example : applyBijection (sptInsert 1 9 (sptInsert 3 4 .ln)) (sptInsert 1 (-2) (sptInsert 3 5 (sptInsert 8 0 .ln))) =
    .bs (.bn .ln (.ls 5)) 0 (.bn (.bn .ln (.ls (-2))) .ln) := by decide +kernel
-- size_ct
example : sizeOfClashTree (.branch (some (sptInsert 7 () .ln)) (.delta [1] [5]) (.seq (.set .ln) (.delta [] []))) =
    6 := by decide +kernel
-- extract
example : extractColoration (sptInsert 1 5 (sptInsert 5 9 .ln)) [1, 5] .ln { colors := [0, 3, 0, 0, 0, 7], int_beg := [], int_end := [], sorted_regs := [], sorted_moves := [] } =
    (.success (.bn .ln (.bn (.bs .ln 3 (.ls 7)) .ln)), { colors := [0, 3, 0, 0, 0, 7], int_beg := [], int_end := [], sorted_regs := [], sorted_moves := [] }) := by decide +kernel
-- run_i
example : runILinearScanHiddenState (colorsSub 1) { colors := (3, 4), int_beg := (0, 0), int_end := (0, 0), sorted_regs := (0, 0), sorted_moves := (0, (0, (0, 0))) } =
    .success 4 := by decide +kernel
-- run_i_fail
example : runILinearScanHiddenState (colorsSub 3) { colors := (3, 4), int_beg := (0, 0), int_end := (0, 0), sorted_regs := (0, 0), sorted_moves := (0, (0, (0, 0))) } =
    .failure .Subscript := by decide +kernel
-- lsra_delta
example : linearScanRegAlloc 3 [] (.delta [1, 5] [2]) [] =
    .success (.bn (.ls 1) (.bs (.ls 0) 1 .ln)) := by decide +kernel
-- lsra_moves
example : linearScanRegAlloc 3 [(1, (1, 5))] (.seq (.delta [5] [1]) (.delta [1] [])) [] =
    .success (.bn .ln (.bs (.ls 1) 0 .ln)) := by decide +kernel
-- lsra_forced
example : linearScanRegAlloc 2 [] (.delta [1, 5, 9] [3]) [(1, 5)] =
    .success (.bn .ln (.bs (.bs .ln 1 (.ls 2)) 0 (.ls 2))) := by decide +kernel
-- lsra_branch_spill
example : linearScanRegAlloc 1 [] (.branch (some (sptInsert 1 () .ln)) (.delta [1] [5]) (.delta [9] [1])) [] =
    .success (.bn .ln (.bs (.bs .ln 0 (.ls 0)) 1 .ln)) := by decide +kernel
-- lsra_phys
example : linearScanRegAlloc 2 [] (.delta [0, 2, 5] [4, 7]) [] =
    .success (.bs (.bs .ln 1 (.ls 2)) 0 (.bn (.ls 3) (.bn .ln (.ls 3)))) := by decide +kernel
-- lsra_stack
example : linearScanRegAlloc 2 [(3, (5, 7))] (.seq (.delta [3, 5] [7, 1]) (.delta [7] [5])) [(5, 1)] =
    .success (.bn .ln (.bs (.ls 1) 0 (.bs .ln 3 (.ls 2)))) := by decide +kernel
end Flapjack.Test.LinearScanTopParity
