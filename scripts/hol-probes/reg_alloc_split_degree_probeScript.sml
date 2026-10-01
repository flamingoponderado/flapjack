(* Original reg_alloc is_not_coalesced and split_degree over a literal
   ra_state. CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble reg_allocTheory;
val _ = Globals.linewidth := 1000;
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val s = ``<| adj_ls := [[];[];[]]; node_tag := [Atemp;Atemp;Atemp]; degrees := [1;5;2]; dim := 3;
   simp_wl := []; spill_wl := []; freeze_wl := []; avail_moves_wl := []; unavail_moves_wl := [];
   coalesced := [0;0;2]; move_related := [F;T;F]; stack := [] |>``;
val _ = observe "inc_self" ``FST (is_not_coalesced 0 ^s)``;
val _ = observe "inc_other" ``FST (is_not_coalesced 1 ^s)``;
val _ = observe "inc_last" ``FST (is_not_coalesced 2 ^s)``;
val _ = observe "inc_oob" ``FST (is_not_coalesced 3 ^s)``;
val _ = observe "sd_low_self" ``FST (split_degree 3 4 0 ^s)``;
val _ = observe "sd_high" ``FST (split_degree 3 4 1 ^s)``;
val _ = observe "sd_low_coalesced_k6" ``FST (split_degree 3 6 1 ^s)``;
val _ = observe "sd_eq_k" ``FST (split_degree 3 2 2 ^s)``;
val _ = observe "sd_out_of_d" ``FST (split_degree 1 4 2 ^s)``;
val _ = observe "sd_oob_bound_true" ``FST (split_degree 10 4 3 ^s)``;
val _ = observe "sd_beyond_all" ``FST (split_degree 3 0 7 ^s)``;
val _ = observe "sd_state" ``SND (split_degree 3 4 0 ^s) = ^s``;
