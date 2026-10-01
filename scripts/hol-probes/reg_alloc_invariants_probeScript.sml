load "bossLib";
load "preamble";
load "reg_allocProofTheory";
open bossLib HolKernel Parse preamble reg_allocTheory reg_allocProofTheory;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val defs = [has_edge_def, undirected_def, good_ra_state_def, no_clash_def, sp_inverts_def,
  is_clique_def, is_subgraph_def, colouring_satisfactory_def, good_pref_def, good_neg_pref_def];
fun holds label term tac =
  (TAC_PROOF (([], term), tac); print (label ^ "="); print "T\n")
  handle HOL_ERR _ =>
    ((TAC_PROOF (([], mk_neg term), tac); print (label ^ "="); print "F\n")
     handle HOL_ERR _ => (print (label ^ "="); print "UNDECIDED\n"));
val fin = rw defs >> fs [NUMERAL_LESS_THM, lookup_insert] >> rw [] >> fs [] >> EVAL_TAC;
val _ = observe "he_hit" ``has_edge [[1];[0]] 0 1``;
val _ = observe "he_miss" ``has_edge [[1];[0]] 0 0``;
val _ = observe "he_y_oob" ``has_edge [[5]] 0 5``;
val _ = observe "he_x_oob" ``has_edge [[1];[0]] 2 1``;
val _ = observe "he_large" ``has_edge [[36893488147419103232];[]] 0 36893488147419103232``;
val _ = holds "und_sym" ``undirected [[1];[0]]`` fin;
val _ = holds "und_asym" ``undirected [[1];[]]`` (rw defs >> qexists_tac `0` >> qexists_tac `1` >> EVAL_TAC);
val _ = holds "grs_ok" ``good_ra_state <| adj_ls := [[1];[0]]; node_tag := [Atemp;Atemp]; degrees := [1;1]; dim := 2; simp_wl := [0]; spill_wl := []; freeze_wl := [1]; avail_moves_wl := [(0,0,1)]; unavail_moves_wl := [(3,1,1)]; coalesced := [0;1]; move_related := [F;F]; stack := [] |>`` fin;
val _ = holds "grs_unsorted" ``good_ra_state <| adj_ls := [[1;2];[0];[0]]; node_tag := [Atemp;Atemp;Atemp]; degrees := [2;1;1]; dim := 3; simp_wl := []; spill_wl := []; freeze_wl := []; avail_moves_wl := []; unavail_moves_wl := []; coalesced := [0;1;2]; move_related := [F;F;F]; stack := [] |>`` (rw defs >> EVAL_TAC);
val _ = holds "grs_bad_move" ``good_ra_state <| adj_ls := [[1];[0]]; node_tag := [Atemp;Atemp]; degrees := [1;1]; dim := 2; simp_wl := []; spill_wl := []; freeze_wl := []; avail_moves_wl := [(0,0,2)]; unavail_moves_wl := []; coalesced := [0;1]; move_related := [F;F]; stack := [] |>`` (rw defs >> EVAL_TAC);
val _ = holds "grs_bad_length" ``good_ra_state <| adj_ls := [[1];[0]]; node_tag := [Atemp]; degrees := [1;1]; dim := 2; simp_wl := []; spill_wl := []; freeze_wl := []; avail_moves_wl := []; unavail_moves_wl := []; coalesced := [0;1]; move_related := [F;F]; stack := [] |>`` (rw defs >> EVAL_TAC);
val _ = holds "nc_ok" ``no_clash [[1];[0]] [Fixed 0; Fixed 1]`` fin;
val _ = holds "nc_clash" ``no_clash [[1];[0]] [Fixed 0; Fixed 0]`` (rw defs >> qexists_tac `0` >> qexists_tac `1` >> EVAL_TAC);
val _ = holds "nc_atemp" ``no_clash [[1];[0]] [Fixed 0; Atemp]`` fin;
val _ = holds "nc_self" ``no_clash [[0]] [Fixed 3]`` fin;
val _ = holds "spi_ok" ``sp_inverts (insert 4 0 LN) (insert 0 4 LN)`` fin;
val _ = holds "spi_bad" ``sp_inverts (insert 4 0 LN) (insert 0 5 LN)`` (rw defs >> qexists_tac `4` >> qexists_tac `0` >> EVAL_TAC);
val _ = holds "spi_insert" ``sp_inverts (insert 7 1 (insert 4 0 LN)) (insert 1 7 (insert 0 4 LN))`` (rw [sp_inverts_def] >> fs [lookup_insert] >> every_case_tac >> fs [lookup_def]);
val _ = holds "clq_ok" ``is_clique [0;1] [[1];[0]]`` fin;
val _ = holds "clq_bad" ``is_clique [0;1;2] [[1];[0];[]]`` (rw defs >> qexists_tac `0` >> qexists_tac `2` >> EVAL_TAC);
val _ = holds "sub_ok" ``is_subgraph [[1];[0]] [[2;1];[0];[]]`` fin;
val _ = holds "sub_bad" ``is_subgraph [[1];[0]] [[1];[]]`` (rw defs >> qexists_tac `1` >> qexists_tac `0` >> EVAL_TAC);
val _ = observe "hide_num" ``hide (36893488147419103232:num)``;
val _ = holds "cs_ok" ``colouring_satisfactory (\x:num. x) [[1];[0]]`` fin;
val _ = holds "cs_bad" ``colouring_satisfactory (\x:num. 0:num) [[1];[0]]`` (rw defs >> qexists_tac `0` >> EVAL_TAC >> qexists_tac `1` >> EVAL_TAC);
val _ = holds "cs_self_loop" ``colouring_satisfactory (\x:num. 0:num) [[0]]`` fin;
val _ = holds "gp_first" ``good_pref (\(n:num) (ks:num list) (s:ra_state). ((M_success (oHD ks)):(num option, state_exn) exc, s))`` (rw defs >> Cases_on `ks` >> EVAL_TAC);
val _ = holds "gp_outside" ``good_pref (\(n:num) (ks:num list) (s:ra_state). ((M_success (SOME 0)):(num option, state_exn) exc, s))`` (rw defs >> TRY (qexists_tac `[]`) >> qexists_tac `<| adj_ls := []; node_tag := []; degrees := []; dim := 0; simp_wl := []; spill_wl := []; freeze_wl := []; avail_moves_wl := []; unavail_moves_wl := []; coalesced := []; move_related := []; stack := [] |>` >> rw defs >> EVAL_TAC);
val _ = holds "gnp_none" ``good_neg_pref 5 (\(n:num) (bads:num list) (s:ra_state). ((M_success NONE):(num option, state_exn) exc, s))`` (rw defs);
val _ = holds "gnp_low" ``good_neg_pref 5 (\(n:num) (bads:num list) (s:ra_state). ((M_success (SOME 4)):(num option, state_exn) exc, s))`` (rw defs >> TRY (qexists_tac `[]`) >> qexists_tac `<| adj_ls := []; node_tag := []; degrees := []; dim := 0; simp_wl := []; spill_wl := []; freeze_wl := []; avail_moves_wl := []; unavail_moves_wl := []; coalesced := []; move_related := []; stack := [] |>` >> rw defs >> EVAL_TAC);
