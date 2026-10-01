import Flapjack.Compiler.Backend.LinearScan.Steps
import Flapjack.Compiler.Backend.LinearScan.Sorting
namespace Flapjack.Test.LinearScanMonadParity
open RegAlloc LinearScan Translator.Monadic.MonadBase
-- Full-value replay of the thirty-four original linear_scan_monad_probe rows on a
-- concrete hidden state (raw sparse-tree constructors). Finite observations only;
-- no allocator soundness or production routing is claimed.
def s0 : LinearScanHiddenState :=
  { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3],
    sorted_regs := [0, 1, 2, 3], sorted_moves := [(5, (1, 2)), (2, (0, 3)), (4, (2, 2))] }
def st0 : LinearScanState :=
  { active := [(-1, 1), (2, 2)], colorpool := [4], phyregs := .ln, colornum := 0,
    colormax := 2, stacknum := 10 }
-- add_if_lt_monad
example : numsetListAddIfLtMonad [0, 1, 3] 2 s0 =
    (.success (), { colors := [7, 8, 9, 6], int_beg := [2, 2, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- add_if_gt_monad
example : numsetListAddIfGtMonad [0, 1, 3] 4 s0 =
    (.success (), { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [4, 4, 6, 4], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- add_if_subscript
example : numsetListAddIfGtMonad [9] 4 s0 =
    (.failure .Subscript, { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- intervals_ct_monad
example : getIntervalsCtMonad (.seq (.delta [1] [2]) (.branch (some (sptInsert 3 () .ln)) (.delta [] [1]) (.set (sptInsert 2 () .ln)))) { s0 with int_beg := [1, 1, 1, 1], int_end := [1, 1, 1, 1] } =
    (.success (-7), { colors := [7, 8, 9, 6], int_beg := [1, -4, -6, -6], int_end := [1, -2, 0, -3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- remove_inactive
example : removeInactiveIntervals 0 st0 s0 =
    (.success { active := [(2,2)], colorpool := [8, 4], phyregs := .ln, colornum := 0, colormax := 2, stacknum := 10 }, { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- add_active
example : addActiveInterval (3, 1) [(1, 0), (5, 2)] =
    [(1,0), (3,1), (5,2)] := by decide +kernel
-- find_color_in_list
example : findColorInList [1, 2, 3] (sptInsert 1 () .ln) =
    some (2,[1, 3]) := by decide +kernel
-- find_color_pool
example : findColor st0 (sptInsert 1 () .ln) =
    ({ active := [(-1,1), (2,2)], colorpool := [], phyregs := .ln, colornum := 0, colormax := 2, stacknum := 10 },some 4) := by decide +kernel
-- find_color_colornum
example : findColor st0 (sptInsert 4 () .ln) =
    ({ active := [(-1,1), (2,2)], colorpool := [4], phyregs := .ln, colornum := 1, colormax := 2, stacknum := 10 },some 0) := by decide +kernel
-- spill
example : spillRegister st0 2 s0 =
    (.success { active := [(-1,1), (2,2)], colorpool := [4], phyregs := .ln, colornum := 0, colormax := 2, stacknum := 11 }, { colors := [7, 8, 10, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- color_phy
example : colorRegister st0 2 5 7 s0 =
    (.success { active := [(-1,1), (2,2), (7,2)], colorpool := [4], phyregs := .bn .ln (.bn (.ls ()) .ln), colornum := 0, colormax := 2, stacknum := 10 }, { colors := [7, 8, 5, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- color_virt
example : colorRegister st0 1 5 7 s0 =
    (.success { active := [(-1,1), (2,2), (7,1)], colorpool := [4], phyregs := .ln, colornum := 0, colormax := 2, stacknum := 10 }, { colors := [7, 5, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- find_last_stealable
example : findLastStealable [(1, 1), (2, 3), (4, 0)] (sptInsert 9 () .ln) s0 =
    (.success (some ((2,3),[(1,1), (4,0)])), { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- find_spill_steal
example : findSpill { st0 with active := [(9, 1)] } (sptInsert 9 () .ln) 3 5 false s0 =
    (.success { active := [(5,3)], colorpool := [4], phyregs := .ln, colornum := 0, colormax := 2, stacknum := 11 }, { colors := [7, 10, 9, 8], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- find_spill_keep
example : findSpill { st0 with active := [(4, 1)] } (sptInsert 9 () .ln) 3 5 false s0 =
    (.success { active := [(4,1)], colorpool := [4], phyregs := .ln, colornum := 0, colormax := 2, stacknum := 11 }, { colors := [7, 8, 9, 10], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- step_aux_pref
example : linearRegAllocStepAux st0 .ln [3, 4] 1 7 false s0 =
    (.success { active := [(-1,1), (2,2), (7,1)], colorpool := [], phyregs := .ln, colornum := 0, colormax := 2, stacknum := 10 }, { colors := [7, 4, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- step_aux_spill
example : linearRegAllocStepAux { st0 with colorpool := [], colornum := 2 } .ln [] 1 7 false s0 =
    (.success { active := [(-1,1), (2,2)], colorpool := [], phyregs := .ln, colornum := 2, colormax := 2, stacknum := 11 }, { colors := [7, 10, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- pass1_phy
example : linearRegAllocStepPass1 .ln .ln (linearRegAllocPass1InitialState 2) 2 s0 =
    (.success { active := [(6,2)], colorpool := [], phyregs := .ls (), colornum := 1, colormax := 2, stacknum := 2 }, { colors := [7, 8, 0, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- pass1_stack
example : linearRegAllocStepPass1 .ln .ln (linearRegAllocPass1InitialState 2) 3 s0 =
    (.success { active := [], colorpool := [], phyregs := .ln, colornum := 0, colormax := 2, stacknum := 3 }, { colors := [7, 8, 9, 2], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- pass1_forced
example : linearRegAllocStepPass1 (sptInsert 1 [0] .ln) (sptInsert 1 [2] .ln) { linearRegAllocPass1InitialState 2 with colorpool := [7, 9] } 1 s0 =
    (.success { active := [(4,1)], colorpool := [7], phyregs := .ln, colornum := 0, colormax := 2, stacknum := 2 }, { colors := [7, 9, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- pass2_virt
example : linearRegAllocStepPass2 .ln (sptInsert 1 [0] .ln) (linearRegAllocPass2InitialState 2 3) 1 s0 =
    (.success { active := [(4,1)], colorpool := [], phyregs := .ln, colornum := 3, colormax := 5, stacknum := 5 }, { colors := [7, 2, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- find_reg_exchange
example : findRegExchange [0, 2] .ln .ln s0 =
    (.success (.bs .ln 7 (.bs (.bn .ln (.ls 1)) 9 (.bn .ln (.ls 0))), .bs .ln 7 (.bs (.bn .ln (.ls 1)) 9 (.bn .ln (.ls 0)))), { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- apply_reg_exchange
example : applyRegExchange [0, 2] s0 =
    (.success (), { colors := [0, 8, 1, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- foldl
example : stExFoldl (state := LinearScanHiddenState) (exception := StateException) (fun e x => ret (e + x)) (0 : Nat) [1, 2, 3] s0 =
    (.success 6, { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- filter_good
example : stExFilterGood (fun r => bind (colorsSub r) (fun col => ret (decide (7 < col)))) [0, 1, 2, 3] s0 =
    (.success [1, 2], { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- edges
example : edgesToAdjlist [(0, 1), (2, 2), (3, 1)] .ln s0 =
    (.success (.bs .ln [1] (.ls [3])), { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- sort_moves_rev
example : sortMovesRev [(5, (1, 2)), (2, (0, 3)), (4, (2, 2))] =
    [(2,0,3), (4,2,2), (5,1,2)] := by decide +kernel
-- sort_regs
example : sortRegs 0 4 s0 =
    (.success (), { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [3, 1, 2, 0], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- sorted_regs_to_list
example : sortedRegsToList 1 3 s0 =
    (.success [1, 2], { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- list_to_sorted_regs
example : listToSortedRegs [3, 2] 1 s0 =
    (.success (), { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 3, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- sort_moves
example : sortMoves 0 3 s0 =
    (.success (), { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(2,0,3), (4,2,2), (5,1,2)] }) := by decide +kernel
-- sorted_moves_to_list
example : sortedMovesToList 0 2 s0 =
    (.success [(5,1,2), (2,0,3)], { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (4,2,2)] }) := by decide +kernel
-- list_to_sorted_moves
example : listToSortedMoves [(1, (1, 1))] 2 s0 =
    (.success (), { colors := [7, 8, 9, 6], int_beg := [3, 1, 2, 0], int_end := [5, 4, 6, 3], sorted_regs := [0, 1, 2, 3], sorted_moves := [(5,1,2), (2,0,3), (1,1,1)] }) := by decide +kernel
-- pass_init
example : (linearRegAllocPass1InitialState 3, linearRegAllocPass2InitialState 3 4) =
    ({ active := [], colorpool := [], phyregs := .ln, colornum := 0, colormax := 3, stacknum := 3 }, { active := [], colorpool := [], phyregs := .ln, colornum := 3, colormax := 7, stacknum := 7 }) := by decide +kernel
end Flapjack.Test.LinearScanMonadParity
