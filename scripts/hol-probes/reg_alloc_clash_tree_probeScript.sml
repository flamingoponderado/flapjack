(* Direct original checker equations; CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble reg_allocTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "delete_names"
  ``numset_list_delete [1;1] (sptree$insert 1 7 (sptree$insert 2 8 sptree$LN)) = sptree$insert 2 8 sptree$LN``;
val _ = print_eval "col_collision"
  ``check_col (K 0) (sptree$insert 1 () (sptree$insert 2 () sptree$LN)) = NONE``;
val _ = print_eval "partial_existing"
  ``check_partial_col (K 0) [1;1] (sptree$insert 1 () sptree$LN) sptree$LN = SOME (sptree$insert 1 () sptree$LN,sptree$LN)``;
val _ = print_eval "partial_collision"
  ``check_partial_col (K 0) [1;2] sptree$LN sptree$LN = NONE``;
val _ = print_eval "delta_discard_writes"
  ``check_clash_tree I (Delta [1] []) sptree$LN sptree$LN = SOME (sptree$LN,sptree$LN)``;
val _ = print_eval "seq_right_first"
  ``check_clash_tree I (Seq (Delta [2] [1]) (Delta [] [2])) sptree$LN sptree$LN = SOME (sptree$insert 1 () sptree$LN,sptree$insert 1 () sptree$LN)``;
val _ = print_eval "branch_merge"
  ``check_clash_tree I (Branch NONE (Delta [] [1]) (Delta [] [2])) sptree$LN sptree$LN = SOME (sptree$insert 2 () (sptree$insert 1 () sptree$LN),sptree$insert 2 () (sptree$insert 1 () sptree$LN))``;
val _ = print_eval "branch_fixed_collision"
  ``check_clash_tree (K 0) (Branch (SOME (sptree$insert 1 () (sptree$insert 2 () sptree$LN))) (Delta [] []) (Delta [] [])) sptree$LN sptree$LN = NONE``;
