import Flapjack.Compiler.Backend.RegAlloc.MovePrep

namespace Flapjack.Test.RegAllocMovePrepParity
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
/-! Same-input kernel replay of fresh original EVAL results
(`scripts/hol-probes/reg_alloc_move_prep_probe.out`) for `extract_color`
(raw sparse result), `coalesce_root`,
`full_consistency_ok` (each rejecting check and an accepted pair) and
`update_move`, including `Subscript` failures. Finite observations do not
establish general cross-prover equivalence. -/

def s : State :=
  { adj_ls := [[1, 2], [0, 3], [0], [1]], node_tag := [.Fixed 1, .Atemp, .Stemp, .Fixed 3],
    degrees := [2, 2, 1, 1], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [],
    avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 2, 1],
    move_related := [false, false, false, false], stack := [] }

-- ec_basic=(M_success (BN (BN (LS 3) LN) (BN (LS 1) (BN LN (LS 0)))),<|adj_ls := [[1; 2]; [0; 3]; [0]; [1]]; node_tag := [Fixed 1; Atemp; Stemp; Fixed ...
example : extractColor (sptInsert 5 0 (sptInsert 6 3 (sptInsert 7 1 .ln))) s =
    (.success (.bn (.bn (.ls 3) .ln) (.bn (.ls 1) (.bn .ln (.ls 0)))),({adj_ls := [[1, 2], [0, 3], [0], [1]], node_tag := [(.Fixed 1), .Atemp, .Stemp, (.Fixed 3)], degrees := [2, 2, 1, 1], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 2, 1], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- ec_oob=M_failure Subscript
example : (extractColor (sptInsert 5 8 .ln) s).1 =
    .failure .Subscript := by decide +kernel
-- cr_self=(M_success 0,<|adj_ls := [[1; 2]; [0; 3]; [0]; [1]]; node_tag := [Fixed 1; Atemp; Stemp; Fixed 3]; degrees := [2; 2; 1; 1]; dim := 4; simp_w...
example : coalesceRoot 0 s =
    (.success 0,({adj_ls := [[1, 2], [0, 3], [0], [1]], node_tag := [(.Fixed 1), .Atemp, .Stemp, (.Fixed 3)], degrees := [2, 2, 1, 1], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 2, 1], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- cr_chain=(M_success 0,<|adj_ls := [[1; 2]; [0; 3]; [0]; [1]]; node_tag := [Atemp; Atemp; Atemp; Atemp]; degrees := [2; 2; 1; 1]; dim := 4; simp_wl :=...
example : coalesceRoot 3 { s with node_tag := [.Atemp, .Atemp, .Atemp, .Atemp] } =
    (.success 0,({adj_ls := [[1, 2], [0, 3], [0], [1]], node_tag := [.Atemp, .Atemp, .Atemp, .Atemp], degrees := [2, 2, 1, 1], dim := 4, simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [], coalesced := [0, 0, 2, 1], move_related := [false, false, false, false], stack := []} : State)) := by decide +kernel
-- cr_fixed=M_success 0
example : (coalesceRoot 3 s).1 =
    .success 0 := by decide +kernel
-- fco_same=M_success F
example : (fullConsistencyOk 2 1 1 s).1 =
    .success false := by decide +kernel
-- fco_out_dim=M_success F
example : (fullConsistencyOk 2 1 4 s).1 =
    .success false := by decide +kernel
-- fco_adjacent=M_success F
example : (fullConsistencyOk 2 0 1 s).1 =
    .success false := by decide +kernel
-- fco_fixed_atemp=M_success F
example : (fullConsistencyOk 2 0 2 { s with node_tag := [.Fixed 1, .Atemp, .Atemp, .Fixed 3] }).1 =
    .success false := by decide +kernel
-- fco_fixed_high=M_success F
example : (fullConsistencyOk 2 3 2 { s with node_tag := [.Fixed 1, .Atemp, .Atemp, .Fixed 3] }).1 =
    .success false := by decide +kernel
-- fco_ok=M_success T
example : (fullConsistencyOk 2 0 3 { s with node_tag := [.Fixed 1, .Atemp, .Atemp, .Atemp] }).1 =
    .success true := by decide +kernel
-- um_order=(4,7,9)
example : updateMove (fun x => 10 - x) (4, (1, 3)) =
    (4,7,9) := by decide +kernel
-- um_keep=(4,1,3)
example : updateMove (fun x => x) (4, (1, 3)) =
    (4,1,3) := by decide +kernel

end Flapjack.Test.RegAllocMovePrepParity
