load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "ca_control" ``let n = insert 1 () LN; e = insert 2 () LN; p = (Seq (MustTerminate (Loop n (Seq (Continue 0) (Break 0)) e)) (If Equal 3 (Reg 4) Tick Skip) : 64 wordLang$prog) in check_clash_tree (\x.x) (get_clash_tree p []) LN LN = SOME (get_live p LN [], get_live p LN [])``;
val _ = observe "ca_return" ``let n = insert 1 () LN; e = insert 2 () LN; p = (Call (SOME ([5],(n,e),MustTerminate (Seq Tick (Loop n (Continue 0) e)),7,8)) (SOME 91) [3;4] NONE : 64 wordLang$prog) in check_clash_tree (\x.x) (get_clash_tree p []) LN LN = SOME (get_live p LN [], get_live p LN [])``;
val _ = observe "ca_handler" ``let n = insert 1 () LN; e = insert 2 () LN; p = (Call (SOME ([5],(n,e),Seq (Assign 6 (Var 7)) Tick,7,8)) (SOME 91) [3] (SOME (5,Loop n (Break 0) e,9,10)) : 64 wordLang$prog) in check_clash_tree (\x.x) (get_clash_tree p []) LN LN = SOME (get_live p LN [], get_live p LN [])``;
val _ = observe "ca_tail_ignored" ``let p = (Call NONE NONE [3;4] (SOME (5,Loop (BN LN LN) Tick (BN LN LN),7,8)) : 64 wordLang$prog) in check_clash_tree (\x.x) (get_clash_tree p []) LN LN = SOME (get_live p LN [], get_live p LN [])``;
val _ = observe "ca_collision" ``check_clash_tree (\x.0) (get_clash_tree (Seq Tick (Call NONE NONE [3;4] NONE) : 64 wordLang$prog) []) LN LN = NONE``;
