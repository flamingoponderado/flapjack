(* Original reg_alloc extract_color, coalesce_root, full_consistency_ok and
   update_move over a literal ra_state. CakeML remains read-only; sparse trees
   print raw. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble reg_allocTheory;
val _ = Globals.linewidth := 1000;
val _ = Parse.temp_remove_user_printer ("sptreepp.sptreepp", ``x : 'a spt``);
fun observe label term = let val th = EVAL term in print (label ^ "="); print_term (rhs (concl th)); print "\n" end;
val s = ``<| adj_ls := [[1;2];[0;3];[0];[1]]; node_tag := [Fixed 1; Atemp; Stemp; Fixed 3]; degrees := [2;2;1;1]; dim := 4;
   simp_wl := []; spill_wl := []; freeze_wl := []; avail_moves_wl := []; unavail_moves_wl := [];
   coalesced := [0;0;2;1]; move_related := [F;F;F;F]; stack := [] |>``;
val _ = observe "ec_basic" ``extract_color (insert 5 0 (insert 6 3 (insert 7 1 LN))) ^s``;
val _ = observe "ec_oob" ``FST (extract_color (insert 5 8 LN) ^s)``;
val _ = observe "cr_self" ``coalesce_root 0 ^s``;
val _ = observe "cr_chain" ``coalesce_root 3 (^s with node_tag := [Atemp; Atemp; Atemp; Atemp])``;
val _ = observe "cr_fixed" ``FST (coalesce_root 3 ^s)``;
val _ = observe "fco_same" ``FST (full_consistency_ok 2 1 1 ^s)``;
val _ = observe "fco_out_dim" ``FST (full_consistency_ok 2 1 4 ^s)``;
val _ = observe "fco_adjacent" ``FST (full_consistency_ok 2 0 1 ^s)``;
val _ = observe "fco_fixed_atemp" ``FST (full_consistency_ok 2 0 2 (^s with node_tag := [Fixed 1; Atemp; Atemp; Fixed 3]))``;
val _ = observe "fco_fixed_high" ``FST (full_consistency_ok 2 3 2 (^s with node_tag := [Fixed 1; Atemp; Atemp; Fixed 3]))``;
val _ = observe "fco_ok" ``FST (full_consistency_ok 2 0 3 (^s with node_tag := [Fixed 1; Atemp; Atemp; Atemp]))``;
val _ = observe "um_order" ``update_move (\x. 10 - x) (4,(1,3))``;
val _ = observe "um_keep" ``update_move (\x. x) (4,(1,3))``;
