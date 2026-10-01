load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "sc_store" ``check_clash_tree (\n.n) (get_clash_tree (ShareInst Store 5 (Var 2) : 64 wordLang$prog) []) LN LN = SOME (insert 5 () (insert 2 () LN),insert 5 () (insert 2 () LN))``;
val _ = observe "sc_store8" ``check_clash_tree (\n.n) (get_clash_tree (ShareInst Store8 5 (Var 2) : 64 wordLang$prog) []) LN LN = SOME (insert 5 () (insert 2 () LN),insert 5 () (insert 2 () LN))``;
val _ = observe "sc_store16" ``check_clash_tree (\n.n) (get_clash_tree (ShareInst Store16 5 (Var 2) : 64 wordLang$prog) []) LN LN = SOME (insert 5 () (insert 2 () LN),insert 5 () (insert 2 () LN))``;
val _ = observe "sc_store32" ``check_clash_tree (\n.n) (get_clash_tree (ShareInst Store32 5 (Var 2) : 64 wordLang$prog) []) LN LN = SOME (insert 5 () (insert 2 () LN),insert 5 () (insert 2 () LN))``;
val _ = observe "sc_load" ``check_clash_tree (\n.n) (get_clash_tree (ShareInst Load 5 (Var 2) : 64 wordLang$prog) []) LN LN = SOME (insert 2 () LN,insert 2 () LN)``;
val _ = observe "sc_load8" ``check_clash_tree (\n.n) (get_clash_tree (ShareInst Load8 5 (Var 2) : 64 wordLang$prog) []) LN LN = SOME (insert 2 () LN,insert 2 () LN)``;
val _ = observe "sc_load16" ``check_clash_tree (\n.n) (get_clash_tree (ShareInst Load16 5 (Var 2) : 64 wordLang$prog) []) LN LN = SOME (insert 2 () LN,insert 2 () LN)``;
val _ = observe "sc_load32" ``check_clash_tree (\n.n) (get_clash_tree (ShareInst Load32 5 (Var 2) : 64 wordLang$prog) []) LN LN = SOME (insert 2 () LN,insert 2 () LN)``;
