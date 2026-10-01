load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q = let val th = EVAL q in
 (print (label ^ "="); print_term (rconc th); print "\n") end;
val env = ``\x:num option. case x of NONE => 99n | SOME k => 10*k+7``;
print_eval "pv_correct_cycle_parallel_1" ``parmove$parsem [(SOME 1,SOME 2);(SOME 2,SOME 1)] ^env (SOME 1)``;
print_eval "pv_correct_cycle_parallel_2" ``parmove$parsem [(SOME 1,SOME 2);(SOME 2,SOME 1)] ^env (SOME 2)``;
print_eval "pv_correct_cycle_parallel_temp" ``parmove$parsem [(SOME 1,SOME 2);(SOME 2,SOME 1)] ^env (NONE)``;
print_eval "pv_correct_cycle_sequential_1" ``parmove$seqsem (REVERSE [(SOME 1,NONE);(SOME 2,SOME 1);(NONE,SOME 2)]) ^env (SOME 1)``;
print_eval "pv_correct_cycle_sequential_2" ``parmove$seqsem (REVERSE [(SOME 1,NONE);(SOME 2,SOME 1);(NONE,SOME 2)]) ^env (SOME 2)``;
print_eval "pv_correct_cycle_sequential_temp" ``parmove$seqsem (REVERSE [(SOME 1,NONE);(SOME 2,SOME 1);(NONE,SOME 2)]) ^env (NONE)``;
print_eval "pv_correct_chain_parallel_1" ``parmove$parsem [(SOME 1,SOME 2);(SOME 2,SOME 3)] ^env (SOME 1)``;
print_eval "pv_correct_chain_parallel_2" ``parmove$parsem [(SOME 1,SOME 2);(SOME 2,SOME 3)] ^env (SOME 2)``;
print_eval "pv_correct_chain_parallel_temp" ``parmove$parsem [(SOME 1,SOME 2);(SOME 2,SOME 3)] ^env (NONE)``;
print_eval "pv_correct_chain_sequential_1" ``parmove$seqsem (REVERSE [(SOME 2,SOME 3);(SOME 1,SOME 2)]) ^env (SOME 1)``;
print_eval "pv_correct_chain_sequential_2" ``parmove$seqsem (REVERSE [(SOME 2,SOME 3);(SOME 1,SOME 2)]) ^env (SOME 2)``;
print_eval "pv_correct_chain_sequential_temp" ``parmove$seqsem (REVERSE [(SOME 2,SOME 3);(SOME 1,SOME 2)]) ^env (NONE)``;
