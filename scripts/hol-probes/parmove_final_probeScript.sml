load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q = let val th = EVAL q in
 (print (label ^ "="); print_term (rconc th); print "\n") end;
print_eval "pv_final_terminal" ``parmove$pmov (([],[],[(SOME 7,NONE)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list)``;
print_eval "pv_final_self" ``parmove$pmov (([(SOME 1,SOME 1)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list)``;
print_eval "pv_final_chain" ``parmove$pmov (([(SOME 1,SOME 2);(SOME 2,SOME 3)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list)``;
print_eval "pv_final_cycle" ``parmove$pmov (([(SOME 1,SOME 2);(SOME 2,SOME 1)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list)``;
print_eval "pv_final_scratch" ``parmove$pmov (([(NONE,SOME 2);(SOME 1,NONE)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list)``;
print_eval "pv_final_duplicate" ``parmove$pmov (([(SOME 1,SOME 2);(SOME 1,SOME 3)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list)``;
print_eval "pv_final_active" ``parmove$pmov (([],[(SOME 1,SOME 2);(SOME 2,NONE)],[(NONE,SOME 1)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list)``;
