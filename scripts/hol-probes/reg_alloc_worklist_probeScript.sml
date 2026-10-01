(* Original reg_alloc degree/worklist/stack updates: dec_deg, dec_degree,
   add_simp_wl, add_spill_wl, add_freeze_wl, push_stack, add_unavail_moves_wl,
   respill, over a literal ra_state. CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble reg_allocTheory;
val _ = Globals.linewidth := 1000;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val s = ``<| adj_ls := [[1;2];[0];[0;0];[]]; node_tag := [Atemp;Atemp;Atemp;Atemp]; degrees := [2;0;5;1]; dim := 3;
   simp_wl := [7]; spill_wl := [8]; freeze_wl := [2;9;2]; avail_moves_wl := []; unavail_moves_wl := [(1,0,1)];
   coalesced := [0;1;2;3]; move_related := [T;T;F;T]; stack := [6] |>``;
val _ = observe "dd_basic" ``dec_deg 0 ^s``;
val _ = observe "dd_zero" ``dec_deg 1 ^s``;
val _ = observe "dd_oob" ``dec_deg 4 ^s``;
val _ = observe "ddeg_basic" ``dec_degree 0 ^s``;
val _ = observe "ddeg_dup" ``dec_degree 2 ^s``;
val _ = observe "ddeg_out_of_dim" ``dec_degree 3 ^s``;
val _ = observe "ddeg_oob_adj" ``dec_degree 0 (^s with adj_ls := [[1;9]])``;
val _ = observe "asw_basic" ``add_simp_wl [1;2] ^s``;
val _ = observe "aspw_basic" ``add_spill_wl [] ^s``;
val _ = observe "afw_basic" ``add_freeze_wl [3] ^s``;
val _ = observe "aum_basic" ``add_unavail_moves_wl [(5,2,3)] ^s``;
val _ = observe "ps_basic" ``push_stack 0 ^s``;
val _ = observe "ps_oob_move_related" ``push_stack 1 (^s with move_related := [T])``;
val _ = observe "ps_oob" ``push_stack 4 ^s``;
val _ = observe "rs_low" ``respill 3 0 ^s``;
val _ = observe "rs_high_frozen" ``respill 3 2 ^s``;
val _ = observe "rs_high_not_frozen" ``respill 1 0 ^s``;
val _ = observe "rs_oob" ``respill 3 4 ^s``;
