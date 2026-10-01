load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "rc_empty" ``let p = (Call (SOME ([],(LN,LN),Skip,7,8)) (NONE) [] NONE : 64 wordLang$prog) in check_clash_tree (\n.n) (get_clash_tree p []) LN LN = SOME (get_live p LN [], get_live p LN [])``;
val _ = observe "rc_cuts" ``let p = (Call (SOME ([5],(insert 1 () LN,insert 2 () LN),Skip,7,8)) (SOME 99) [3;4] NONE : 64 wordLang$prog) in check_clash_tree (\n.n) (get_clash_tree p []) LN LN = SOME (get_live p LN [], get_live p LN [])``;
val _ = observe "rc_duplicate_args" ``let p = (Call (SOME ([5;5],(insert 1 () LN,insert 2 () LN),Skip,7,8)) (NONE) [3;3;4] NONE : 64 wordLang$prog) in check_clash_tree (\n.n) (get_clash_tree p []) LN LN = SOME (get_live p LN [], get_live p LN [])``;
val _ = observe "rc_return_tick" ``let p = (Call (SOME ([5],(LN,LN),Tick,7,8)) (SOME 0) [3] NONE : 64 wordLang$prog) in check_clash_tree (\n.n) (get_clash_tree p []) LN LN = SOME (get_live p LN [], get_live p LN [])``;
val _ = observe "rc_return_break" ``let p = (Call (SOME ([5],(LN,LN),Break 0,7,8)) (NONE) [3] NONE : 64 wordLang$prog) in check_clash_tree (\n.n) (get_clash_tree p [(insert 8 () LN,insert 9 () LN)]) LN LN = SOME (get_live p LN [(insert 8 () LN,insert 9 () LN)], get_live p LN [(insert 8 () LN,insert 9 () LN)])``;
val _ = observe "rc_return_collision" ``let p = (Call (SOME ([5;6],(LN,LN),Skip,7,8)) (NONE) [] NONE : 64 wordLang$prog) in check_clash_tree (\n.0) (get_clash_tree p []) LN LN = NONE``;
val _ = observe "rc_args_collision" ``let p = (Call (SOME ([],(LN,LN),Skip,7,8)) (NONE) [3;4] NONE : 64 wordLang$prog) in check_clash_tree (\n.0) (get_clash_tree p []) LN LN = NONE``;
