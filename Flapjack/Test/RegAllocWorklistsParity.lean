import Flapjack.Compiler.Backend.RegAlloc.Worklists

namespace Flapjack.Test.RegAllocWorklistsParity
open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
/-! Same-input kernel replay of fresh original EVAL results
(`scripts/hol-probes/reg_alloc_worklist_probe.out`) for `dec_deg` (truncated
decrement), `dec_degree` (duplicate neighbours, out-of-dimension no-op,
out-of-array neighbour), the `add_*_wl` prepends, `push_stack` (including a
partial update before failure) and `respill`, with full `ra_state` results.
Finite observations do not establish general cross-prover equivalence. -/

def s : State :=
  { adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp],
    degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2],
    avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3],
    move_related := [true, true, false, true], stack := [6] }

-- dd_basic=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [1; 0; 5; 1]; dim := 3; simp_wl :=...
example : decDeg 0 s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [1, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- dd_zero=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl :=...
example : decDeg 1 s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- dd_oob=(M_failure Subscript,<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; sim...
example : decDeg 4 s =
    (.failure .Subscript,({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- ddeg_basic=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 4; 1]; dim := 3; simp_wl :=...
example : decDegree 0 s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 4, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- ddeg_dup=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 5; 1]; dim := 3; simp_wl :=...
example : decDegree 2 s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- ddeg_out_of_dim=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl :=...
example : decDegree 3 s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- ddeg_oob_adj=(M_failure Subscript,<|adj_ls := [[1; 9]]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl := [7]; spil...
example : decDegree 0 { s with adj_ls := [[1, 9]] } =
    (.failure .Subscript,({adj_ls := [[1, 9]], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- asw_basic=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl :=...
example : addSimpWl (γ := StateException) [1, 2] s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [1, 2, 7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- aspw_basic=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl :=...
example : addSpillWl (γ := StateException) [] s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- afw_basic=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl :=...
example : addFreezeWl (γ := StateException) [3] s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [3, 2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- aum_basic=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl :=...
example : addUnavailMovesWl (γ := StateException) [(5, (2, 3))] s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(5, (2, 3)), (1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- ps_basic=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 5; 1]; dim := 3; simp_wl :=...
example : pushStack 0 s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [false, true, false, true], stack := [0, 6]} : State)) := by decide +kernel
-- ps_oob_move_related=(M_failure Subscript,<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; sim...
example : pushStack 1 { s with move_related := [true] } =
    (.failure .Subscript,({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true], stack := [6]} : State)) := by decide +kernel
-- ps_oob=(M_failure Subscript,<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; sim...
example : pushStack 4 s =
    (.failure .Subscript,({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- rs_low=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl :=...
example : respill 3 0 s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- rs_high_frozen=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl :=...
example : respill 3 2 s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [2, 8], freeze_wl := [9], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- rs_high_not_frozen=(M_success (),<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; simp_wl :=...
example : respill 1 0 s =
    (.success (),({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel
-- rs_oob=(M_failure Subscript,<|adj_ls := [[1; 2]; [0]; [0; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 0; 5; 1]; dim := 3; sim...
example : respill 3 4 s =
    (.failure .Subscript,({adj_ls := [[1, 2], [0], [0, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 0, 5, 1], dim := 3, simp_wl := [7], spill_wl := [8], freeze_wl := [2, 9, 2], avail_moves_wl := [], unavail_moves_wl := [(1, (0, 1))], coalesced := [0, 1, 2, 3], move_related := [true, true, false, true], stack := [6]} : State)) := by decide +kernel

/-! The four worklist prepends are exception-polymorphic, as their original HOL
types are (`... -> ra_state -> (unit, 'a) exc # ra_state`, rows `*_type` of the
probe): the same results at the unrelated exception carriers `Bool` and `Nat`. -/
example : addSimpWl (γ := Bool) [1, 2] s = (.success (), { s with simp_wl := [1, 2, 7] }) := by
  decide +kernel
example : addSpillWl (γ := Nat) [4] s = (.success (), { s with spill_wl := [4, 8] }) := by
  decide +kernel
example : addFreezeWl (γ := Bool) [3] s = (.success (), { s with freeze_wl := [3, 2, 9, 2] }) := by
  decide +kernel
example : addUnavailMovesWl (γ := Nat) [(5, (2, 3))] s =
    (.success (), { s with unavail_moves_wl := [(5, (2, 3)), (1, (0, 1))] }) := by
  decide +kernel

end Flapjack.Test.RegAllocWorklistsParity
