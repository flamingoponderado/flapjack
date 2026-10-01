load "bossLib"; load "preamble"; load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun observe label term = (print (label ^ "="); print_term (rconc (EVAL term)); print "\n");
val _ = observe "pmm_shared" ``MEM (SOME 3) (MAP FST (parmove [(1:num,2);(3,2)]))``;
val _ = observe "pmm_cycle" ``MEM (SOME 1) (MAP FST (parmove [(1:num,2);(2,1)]))``;
val _ = observe "pmm_bool" ``MEM (SOME F) (MAP FST (parmove [(F,T)]))``;
val _ = observe "pmm_output" ``parmove [(1:num,2);(3,2)] = [(SOME 1,SOME 2);(SOME 3,SOME 2)]``;
val _ = observe "pmm_self" ``parmove [(4:num,4)] = []``;
val _ = observe "pmm_empty" ``parmove ([] : (num # num) list) = []``;
