load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "lc_break_absent" ``check_clash_tree (\n.n) (get_clash_tree (Break 2 : 64 word prog) []) LN LN = SOME (LN,LN)``;
val _ = observe "lc_continue_absent" ``check_clash_tree (\n.n) (get_clash_tree (Continue 2 : 64 word prog) []) LN LN = SOME (LN,LN)``;
val _ = observe "lc_break_present" ``check_clash_tree (\n.n) (get_clash_tree (Break 0 : 64 word prog) [(insert 1 () LN,insert 2 () LN)]) LN LN = SOME (insert 2 () LN,insert 2 () LN)``;
val _ = observe "lc_continue_present" ``check_clash_tree (\n.n) (get_clash_tree (Continue 0 : 64 word prog) [(insert 1 () LN,insert 2 () LN)]) LN LN = SOME (insert 1 () LN,insert 1 () LN)``;
val _ = observe "lc_loop_skip" ``check_clash_tree (\n.n) (get_clash_tree (Loop (insert 1 () LN) Skip (insert 2 () LN) : 64 word prog) []) LN LN = SOME (insert 1 () LN,insert 1 () LN)``;
val _ = observe "lc_loop_continue" ``check_clash_tree (\n.n) (get_clash_tree (Loop (insert 1 () LN) (Continue 0) (insert 2 () LN) : 64 word prog) []) LN LN = SOME (insert 1 () LN,insert 1 () LN)``;
val _ = observe "lc_break_collision" ``check_clash_tree (\n.0) (get_clash_tree (Break 0 : 64 word prog) [(LN,insert 1 () (insert 2 () LN))]) LN LN = NONE``;
