(* Direct original linear_scan pure live-tree/interval equations; CakeML remains read-only. *)
load "bossLib";
load "preamble";
load "linear_scanTheory";
open bossLib HolKernel Parse preamble linear_scanTheory;
fun print_eval label q =
  let val th = EVAL q in
    print (label ^ "="); print (term_to_string (rconc th)); print "\n"
  end;
val _ = print_eval "get_live_tree_branch_cut"
  ``get_live_tree (Branch (SOME (insert 3 () LN)) (Delta [1] [2]) (Set (insert 5 () (insert 4 () LN)))) = Seq (Reads [3]) (Branch (Seq (Reads [2]) (Writes [1])) (Reads [5; 4]))``;
val _ = print_eval "get_live_backward_branch"
  ``get_live_backward (Seq (Writes [1]) (Branch (Reads [2;1]) (Reads [3]))) LN = BN (LS ()) (BN LN (LS ()))``;
val _ = print_eval "fix_domination_reads"
  ``fix_domination (Reads [1]) = Seq (Writes [1]) (Reads [1])``;
val _ = print_eval "fix_domination_writes"
  ``fix_domination (Writes [1]) = Writes [1]``;
val _ = print_eval "check_live_tree_seq"
  ``check_live_tree I (Seq (Writes [2]) (Reads [1;2])) LN LN = SOME (BN LN (LS ()), BN LN (LS ()))``;
val _ = print_eval "check_live_tree_collision"
  ``check_live_tree (K 0) (Seq (Writes [2]) (Reads [1;2])) LN LN = NONE``;
val _ = print_eval "check_live_tree_branch"
  ``check_live_tree I (Branch (Reads [1]) (Reads [2])) LN LN = SOME (BN (LS ()) (LS ()), BN (LS ()) (LS ()))``;
val _ = print_eval "add_if_lt"
  ``numset_list_add_if_lt [1;2;1] 5 (insert 1 7 LN) = BN (LS 5) (LS 5)``;
val _ = print_eval "add_if_gt"
  ``numset_list_add_if_gt [1;2;1] 5 (insert 1 7 LN) = BN (LS 5) (LS 7)``;
val _ = print_eval "get_intervals_seq"
  ``get_intervals (Seq (Writes [1]) (Reads [1;2])) 0 LN LN = (-2, BN LN (LS (-1)), BN (LS 0) (LS 0))``;
val _ = print_eval "get_intervals_withlive_branch"
  ``get_intervals_withlive (Branch (Reads [1]) (Writes [2])) 0 LN LN (insert 2 () LN) = (-2, LN, BN (LS 0) (LS (-1)))``;
val _ = print_eval "get_intervals_ct"
  ``get_intervals_ct (Seq (Delta [1] [2]) (Branch (SOME (insert 3 () LN)) (Delta [] [1]) (Set (insert 2 () LN)))) = (-7, BN (LS (-6)) (BS LN (-4) (LS (-6))), BN (LS 0) (BS LN (-2) (LS (-3))))``;
val _ = print_eval "size_of_live_tree"
  ``size_of_live_tree (Seq (Writes [1]) (Branch (Reads [2;1]) (Reads [3]))) = 3``;
val _ = print_eval "numset_list_insert_nottailrec"
  ``numset_list_insert_nottailrec [4;1;2] LN = BN (BS LN () (LS ())) (LS ())``;
val _ = print_eval "numset_list_insert"
  ``numset_list_insert [4;1;2] LN = BN (BS LN () (LS ())) (LS ())``;
