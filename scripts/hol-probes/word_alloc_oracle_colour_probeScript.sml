load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib HolKernel Parse preamble word_allocTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "oc_none" ``oracle_colour_ok 0 (NONE) (Delta [] []) (Skip : 64 wordLang$prog) [] = (NONE)``;
val _ = observe "oc_empty" ``oracle_colour_ok 0 (SOME LN) (Delta [] []) (Skip : 64 wordLang$prog) [] = (SOME Skip)``;
val _ = observe "oc_physical_bad" ``oracle_colour_ok 0 (SOME (insert 2 99 LN)) (Delta [] []) (Skip : 64 wordLang$prog) [] = (NONE)``;
val _ = observe "oc_checker_collision" ``oracle_colour_ok 0 (SOME LN) (Set (insert 3 () (insert 5 () LN))) (Skip : 64 wordLang$prog) [] = (NONE)``;
val _ = observe "oc_forced_collision" ``oracle_colour_ok 0 (SOME LN) (Delta [] []) (Skip : 64 wordLang$prog) [(3,5)] = (NONE)``;
val _ = observe "oc_forced_distinct" ``oracle_colour_ok 0 (SOME LN) (Delta [] []) (Skip : 64 wordLang$prog) [(2,4)] = (SOME Skip)``;
val _ = observe "oc_rename" ``oracle_colour_ok 0 (SOME (insert 3 4 (insert 5 7 LN))) (Delta [] []) (Assign 3 (Var 5) : 64 wordLang$prog) [] = (SOME (Assign 8 (Var 14)))``;
val _ = observe "oc_stack_equal" ``oracle_colour_ok 4 (SOME (insert 3 4 LN)) (Delta [] []) (Alloc 3 (insert 3 () LN,LN) : 64 wordLang$prog) [] = (SOME (Alloc 8 (insert 8 () LN,LN)))``;
val _ = observe "oc_stack_below" ``oracle_colour_ok 5 (SOME (insert 3 4 LN)) (Delta [] []) (Alloc 3 (insert 3 () LN,LN) : 64 wordLang$prog) [] = (NONE)``;
val _ = observe "oc_raw_map" ``oracle_colour_ok 0 (SOME (BN LN LN)) (Delta [] []) (Skip : 64 wordLang$prog) [] = (SOME Skip)``;
