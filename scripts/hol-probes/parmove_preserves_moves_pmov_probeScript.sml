load "bossLib"; load "preamble"; load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun observe label term = (print (label ^ "="); print_term (rconc (EVAL term)); print "\n");
val _ = observe "pmv_terminal" ``MEM NONE (MAP FST (state_to_list (pmov (([],[],[(NONE,SOME 7)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
val _ = observe "pmv_pending" ``MEM (SOME 3) (MAP FST (state_to_list (pmov (([(SOME 1,SOME 2);(SOME 3,SOME 2)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
val _ = observe "pmv_output" ``pmov (([(SOME 1,SOME 2);(SOME 3,SOME 2)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list) = ([],[],[(SOME 3,SOME 2);(SOME 1,SOME 2)])``;
