import Flapjack.Compiler.Backend.RegAlloc.Coalesce
import Flapjack.Compiler.Backend.RegAlloc.SpillChoice

namespace Flapjack.Test.RegAllocCoalesceParity
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

-- The `st_ex_FIRST` result type nests options, products and lists; the default
-- instance-search size is too small to assemble its `DecidableEq`.
set_option synthInstance.maxSize 1024
/-! Same-input kernel replay of fresh original EVAL results
(`scripts/hol-probes/reg_alloc_coalesce_probe.out`) for misc `lookup_any`,
`inc_deg`, `consistency_ok` (each rejecting check), `coalesce_parent` (self,
compressed chain, fixed, forward pointer), `canonize_move`, `st_ex_FIRST`
(empty, NONE-then-SOME with canonicalised unavail, all rejected),
`reset_move_related`, `st_ex_list_MAX_deg` and `st_ex_list_MIN_cost`, with full
`ra_state` results including `Subscript` failures. Finite observations do not
establish general cross-prover equivalence. -/

def s : State :=
  { adj_ls := [[2], [], [0], [], []], node_tag := [.Fixed 0, .Atemp, .Atemp, .Atemp, .Atemp],
    degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [],
    avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4],
    move_related := [false, true, true, false, true], stack := [] }

-- la_hit=7
example : lookupAny 3 (sptInsert 3 (7 : Nat) .ln) 0 =
    7 := by decide +kernel
-- la_miss=9
example : lookupAny 2 (sptInsert 3 (7 : Nat) .ln) 9 =
    9 := by decide +kernel
-- la_bool=T
example : lookupAny 0 (.ln : Spt Bool) true =
    true := by decide +kernel
-- id_basic=(M_success (),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 6; 4; 1; 5]; dim := 5; s...
example : incDeg 1 5 s =
    (.success (),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 6, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- id_oob=(M_failure Subscript,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim ...
example : incDeg 5 1 s =
    (.failure .Subscript,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- co_same=(M_success F,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; si...
example : consistencyOk 1 1 s =
    (.success false,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- co_adjacent=(M_success F,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; si...
example : consistencyOk 0 2 s =
    (.success false,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- co_fixed_mr=(M_success T,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; si...
example : consistencyOk 0 1 s =
    (.success true,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- co_not_mr=(M_success F,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; si...
example : consistencyOk 3 1 s =
    (.success false,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- co_both_mr=(M_success T,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; si...
example : consistencyOk 1 4 s =
    (.success true,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- co_oob=(M_failure Subscript,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim ...
example : consistencyOk 1 7 s =
    (.failure .Subscript,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- cp_self=(M_success 1,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; si...
example : coalesceParent 1 s =
    (.success 1,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- cp_chain=(M_success 1,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; si...
example : coalesceParent 3 s =
    (.success 1,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 1, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- cp_fixed=(M_success 0,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; si...
example : coalesceParent 0 s =
    (.success 0,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- cp_forward=(M_success 1,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; si...
example : coalesceParent 1 { s with coalesced := [0, 3, 1, 3, 4] } =
    (.success 1,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 3, 1, 3, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- cp_oob=(M_failure Subscript,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim ...
example : coalesceParent 9 s =
    (.failure .Subscript,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- cm_fixed_second=(M_success (0,2),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5...
example : canonizeMove 2 0 s =
    (.success (0,2),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- cm_fixed_first=(M_success (0,2),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5...
example : canonizeMove 0 2 s =
    (.success (0,2),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- cm_order=(M_success (1,4),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5...
example : canonizeMove 4 1 s =
    (.success (1,4),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- sf_empty=(M_success (NONE,[(9,9,9)]),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5...
example : stExFirst consistencyOk (fun x y => ret (some (x + y))) ([] : List (Nat × Nat × Nat)) [(9, 9, 9)] s =
    (.success (none,[(9,9,9)]),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- sf_first=(M_success (SOME ((0,4),T,[(3,3,1)]),[(1,1,4)]),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degre...
example : stExFirst consistencyOk (fun x _ => ret (if x = 1 then none else some true)) [(1, 1, 4), (2, 4, 0), (3, 3, 1)] [] s =
    (.success (some ((0,4),true,[(3,3,1)]),[(1,1,4)]),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- sf_none=(M_success (NONE,[]),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim ...
example : stExFirst (fun _ _ => ret false) (fun _ _ => ret (some ())) [(true, 1, 4), (false, 3, 1)] [] s =
    (.success (none,[]),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 1, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- rmr_basic=(M_success (),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim := 5; s...
example : resetMoveRelated [(7, 0, 2), (8, 3, 4)] s =
    (.success (),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, false, true, true, true], stack := []} : State)) := by decide +kernel
-- rmr_oob=(M_failure Subscript,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; dim ...
example : resetMoveRelated [(7, 0, 9)] s =
    (.failure .Subscript,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, false, false, false, false], stack := []} : State)) := by decide +kernel
-- maxd_basic=(M_success (4,[2; 0; 1]),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; ...
example : stExListMaxDeg [1, 2, 9, 4] 5 0 3 [] s =
    (.success (4,[2, 0, 1]),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- maxd_tie=(M_success (2,[1; 3; 8]),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; ...
example : stExListMaxDeg [3, 1] 5 2 1 [8] s =
    (.success (2,[1, 3, 8]),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- maxd_oob_dim=(M_failure Subscript,<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [1]; dim := 5; simp_w...
example : stExListMaxDeg [2] 7 0 0 [] { s with degrees := [1] } =
    (.failure .Subscript,({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [1], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- minc_basic=(M_success (4,[2; 0; 1]),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3; 1; 4; 1; 5]; ...
example : stExListMinCost (sptInsert 1 10 (sptInsert 2 4 .ln)) [1, 2, 9, 4] 5 0 6 [] s =
    (.success (4,[2, 0, 1]),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [3, 1, 4, 1, 5], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel
-- minc_zero_deg=(M_success (1,[0]),<|adj_ls := [[2]; []; [0]; []; []]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0]; dim := 5; simp_...
example : stExListMinCost (sptInsert 1 10 .ln) [1] 5 0 6 [] { s with degrees := [0, 0] } =
    (.success (1,[0]),({adj_ls := [[2], [], [0], [], []], node_tag := [(.Fixed 0), .Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0], dim := 5, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 1, 1, 2, 4], move_related := [false, true, true, false, true], stack := []} : State)) := by decide +kernel

end Flapjack.Test.RegAllocCoalesceParity
