(* Original reg_alloc coalescing and spill-choice helpers over a literal
   ra_state: inc_deg, consistency_ok, coalesce_parent, canonize_move,
   st_ex_FIRST, reset_move_related, st_ex_list_MAX_deg, st_ex_list_MIN_cost,
   and misc lookup_any. CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble reg_allocTheory;
val _ = Globals.linewidth := 1000;
val _ = Parse.temp_remove_user_printer ("sptreepp.sptreepp", ``x : 'a spt``);
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val s = ``<| adj_ls := [[2];[];[0];[];[]]; node_tag := [Fixed 0; Atemp; Atemp; Atemp; Atemp]; degrees := [3;1;4;1;5]; dim := 5;
   simp_wl := []; spill_wl := []; freeze_wl := []; avail_moves_wl := []; unavail_moves_wl := [];
   coalesced := [0;1;1;2;4]; move_related := [F;T;T;F;T]; stack := [] |>``;
val _ = observe "la_hit" ``lookup_any 3 (insert 3 (7:num) LN) 0``;
val _ = observe "la_miss" ``lookup_any 2 (insert 3 (7:num) LN) 9``;
val _ = observe "la_bool" ``lookup_any 0 (LN:bool num_map) T``;
val _ = observe "id_basic" ``inc_deg 1 5 ^s``;
val _ = observe "id_oob" ``inc_deg 5 1 ^s``;
val _ = observe "co_same" ``consistency_ok 1 1 ^s``;
val _ = observe "co_adjacent" ``consistency_ok 0 2 ^s``;
val _ = observe "co_fixed_mr" ``consistency_ok 0 1 ^s``;
val _ = observe "co_not_mr" ``consistency_ok 3 1 ^s``;
val _ = observe "co_both_mr" ``consistency_ok 1 4 ^s``;
val _ = observe "co_oob" ``consistency_ok 1 7 ^s``;
val _ = observe "cp_self" ``coalesce_parent 1 ^s``;
val _ = observe "cp_chain" ``coalesce_parent 3 ^s``;
val _ = observe "cp_fixed" ``coalesce_parent 0 ^s``;
val _ = observe "cp_forward" ``coalesce_parent 1 (^s with coalesced := [0;3;1;3;4])``;
val _ = observe "cp_oob" ``coalesce_parent 9 ^s``;
val _ = observe "cm_fixed_second" ``canonize_move 2 0 ^s``;
val _ = observe "cm_fixed_first" ``canonize_move 0 2 ^s``;
val _ = observe "cm_order" ``canonize_move 4 1 ^s``;
val _ = observe "sf_empty" ``st_ex_FIRST consistency_ok (\x y. st_ex_return (SOME (x+y))) ([]:(num#num#num) list) [(9,9,9)] ^s``;
val _ = observe "sf_first" ``st_ex_FIRST consistency_ok (\x y. st_ex_return (if x = 1 then NONE else SOME T)) [(1,1,4);(2,4,0);(3,3,1)] [] ^s``;
val _ = observe "sf_none" ``st_ex_FIRST (\x y. st_ex_return F) (\x y. st_ex_return (SOME ())) [(T,1,4);(F,3,1)] [] ^s``;
val _ = observe "rmr_basic" ``reset_move_related [(7,0,2);(8,3,4)] ^s``;
val _ = observe "rmr_oob" ``reset_move_related [(7,0,9)] ^s``;
val _ = observe "maxd_basic" ``st_ex_list_MAX_deg [1;2;9;4] 5 0 3 [] ^s``;
val _ = observe "maxd_tie" ``st_ex_list_MAX_deg [3;1] 5 2 1 [8] ^s``;
val _ = observe "maxd_oob_dim" ``st_ex_list_MAX_deg [2] 7 0 0 [] (^s with degrees := [1])``;
val _ = observe "minc_basic" ``st_ex_list_MIN_cost (insert 1 10 (insert 2 4 LN)) [1;2;9;4] 5 0 6 [] ^s``;
val _ = observe "minc_zero_deg" ``st_ex_list_MIN_cost (insert 1 10 LN) [1] 5 0 6 [] (^s with degrees := [0;0])``;
