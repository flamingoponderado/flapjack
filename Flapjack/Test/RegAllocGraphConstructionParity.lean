import Flapjack.Compiler.Backend.RegAlloc.GraphConstruction

namespace Flapjack.Test.RegAllocGraphConstructionParity
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
/-! Same-input kernel replay of fresh original EVAL results
(`scripts/hol-probes/reg_alloc_graph_construction_probe.out`) for
`insert_edge`, `list_insert_edge`, `clique_insert_edge`, `extend_clique`,
`mk_tags`, `mk_graph` (every clash-tree constructor), `extend_graph` (Bool
endpoints) and `init_ra_state`, with full `ra_state` results, including every
`Subscript` failure and its retained partial state. Finite observations do not
establish general cross-prover equivalence. -/

/-- HOL probe `st n`: `n` empty adjacency lists, `Atemp` tags, zero degrees,
coalesced and false move flags, empty worklists. -/
def st (n : Nat) : State :=
  { adj_ls := List.replicate n [], node_tag := List.replicate n .Atemp,
    degrees := List.replicate n 0, dim := n, simp_wl := [], spill_wl := [],
    freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [],
    coalesced := List.replicate n 0, move_related := List.replicate n false, stack := [] }

abbrev s4 : State := st 4
abbrev s3 : State := st 3

-- ie_basic=(M_success (),<|adj_ls := [[2]; []; [0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill_wl := ...
example : insertEdge 0 2 s4 =
    (.success (),({adj_ls := [[2], [], [0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- ie_self=(M_success (),<|adj_ls := [[]; [1]; []; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill_wl := [...
example : insertEdge 1 1 s4 =
    (.success (),({adj_ls := [[], [1], [], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- ie_oob=(M_failure Subscript,<|adj_ls := [[]; []; []; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill_w...
example : insertEdge 0 7 s4 =
    (.failure .Subscript,({adj_ls := [[], [], [], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- ie_oob_first=(M_failure Subscript,<|adj_ls := [[]; []; []; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill_w...
example : insertEdge 9 0 s4 =
    (.failure .Subscript,({adj_ls := [[], [], [], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- lie_basic=(M_success (),<|adj_ls := [[3]; [3]; []; [3; 1; 0]]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill...
example : listInsertEdge 3 [0, 1, 3] s4 =
    (.success (),({adj_ls := [[3], [3], [], [3, 1, 0]], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- lie_fail_mid=(M_failure Subscript,<|adj_ls := [[1]; [0]; []; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill...
example : listInsertEdge 0 [1, 8, 2] s4 =
    (.failure .Subscript,({adj_ls := [[1], [0], [], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- cie_basic=(M_success (),<|adj_ls := [[2; 1]; [2; 0]; [1; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; sp...
example : cliqueInsertEdge [0, 1, 2] s4 =
    (.success (),({adj_ls := [[2, 1], [2, 0], [1, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- ec_basic=(M_success [3; 2; 0; 1],<|adj_ls := [[3; 2]; [3; 2]; [3; 1; 0]; [2; 1; 0]]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := ...
example : extendClique [2, 0, 3, 2] [0, 1] s4 =
    (.success [3, 2, 0, 1],({adj_ls := [[3, 2], [3, 2], [3, 1, 0], [2, 1, 0]], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- ec_fail=(M_failure Subscript,<|adj_ls := [[1]; [0]; []; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill...
example : extendClique [1, 5] [0] s4 =
    (.failure .Subscript,({adj_ls := [[1], [0], [], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- mt_basic=(M_success (),<|adj_ls := [[]; []; []; []]; node_tag := [Stemp; Atemp; Stemp; Fixed 2]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill_wl := ...
example : mkTags 4 (sptInsert 5 () .ln) (fun i => if i = 0 then 5 else if i = 1 then 9 else if i = 2 then 3 else 4) s4 =
    (.success (),({adj_ls := [[], [], [], []], node_tag := [.Stemp, .Atemp, .Stemp, (.Fixed 2)], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- mt_oob=(M_failure Subscript,<|adj_ls := [[]; []; []; []]; node_tag := [Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill_wl := []; freeze_wl :=...
example : mkTags 2 .ln (fun i => i * 4 + 1) { s4 with node_tag := [.Stemp] } =
    (.failure .Subscript,({adj_ls := [[], [], [], []], node_tag := [.Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- mg_delta=(M_success [2; 3],<|adj_ls := [[3; 1]; [3; 0]; [3]; [2; 1; 0]]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl :...
example : mkGraph (fun x => x) (.delta [0, 1] [2]) [3] s4 =
    (.success [2, 3],({adj_ls := [[3, 1], [3, 0], [3], [2, 1, 0]], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- mg_set=(M_success [1; 3],<|adj_ls := [[]; [3]; []; [1]]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill_wl...
example : mkGraph (fun x => x / 2) (.set (sptInsert 2 () (sptInsert 6 () .ln))) [] s4 =
    (.success [1, 3],({adj_ls := [[], [3], [], [1]], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- mg_branch_none=(M_success [0; 1; 2],<|adj_ls := [[2; 1]; [2; 0]; [1; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl :=...
example : mkGraph (fun x => x) (.branch none (.delta [] [0, 1]) (.delta [] [2])) [] s4 =
    (.success [0, 1, 2],({adj_ls := [[2, 1], [2, 0], [1, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- mg_branch_some=(M_success [3],<|adj_ls := [[2]; [2]; [1; 0]; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill_w...
example : mkGraph (fun x => x) (.branch (some (sptInsert 3 () .ln)) (.delta [] [0]) (.delta [] [1])) [2] s4 =
    (.success [3],({adj_ls := [[2], [2], [1, 0], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- mg_seq=(M_success [1; 3; 2],<|adj_ls := [[3; 2]; [3; 2]; [3; 1; 0]; [2; 1; 0]]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; ...
example : mkGraph (fun x => x) (.seq (.delta [0] [1]) (.delta [1] [2, 3])) [] s4 =
    (.success [1, 3, 2],({adj_ls := [[3, 2], [3, 2], [3, 1, 0], [2, 1, 0]], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- mg_fail=(M_failure Subscript,<|adj_ls := [[1]; [0]; []; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill...
example : mkGraph (fun x => x) (.delta [0] [9]) [1] s4 =
    (.failure .Subscript,({adj_ls := [[1], [0], [], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- eg_basic=(M_success (),<|adj_ls := [[]; [3]; []; [3; 1]]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill_wl ...
example : extendGraph (fun b : Bool => if b then 1 else 3) [(true, false), (false, false)] s4 =
    (.success (),({adj_ls := [[], [3], [], [3, 1]], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- eg_fail=(M_failure Subscript,<|adj_ls := [[1]; [0]; []; []]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [0; 0; 0; 0]; dim := 4; simp_wl := []; spill...
example : extendGraph (fun x : Nat => x) [(0, 1), (2, 6)] s4 =
    (.failure .Subscript,({adj_ls := [[1], [0], [], []], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [0, 0, 0, 0], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0, 0], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- ira_basic=(M_success (),<|adj_ls := [[2; 1]; [2; 0]; [1; 0]]; node_tag := [Stemp; Atemp; Stemp]; degrees := [0; 0; 0]; dim := 3; simp_wl := []; spill_wl := []; ...
example : initRaState (.seq (.delta [5] [1]) (.set (sptInsert 1 () (sptInsert 3 () .ln)))) [(5, 3)] (sptInsert 1 () .ln) (sptInsert 1 0 (sptInsert 3 2 (sptInsert 5 1 .ln)), sptInsert 0 1 (sptInsert 1 5 (sptInsert 2 3 .ln)), 3) s3 =
    (.success (),({adj_ls := [[2, 1], [2, 0], [1, 0]], node_tag := [.Stemp, .Atemp, .Stemp], degrees := [0, 0, 0], dim := 3, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 0], move_related := [false, false, false], stack := []} : State)) := by decide +kernel

end Flapjack.Test.RegAllocGraphConstructionParity
