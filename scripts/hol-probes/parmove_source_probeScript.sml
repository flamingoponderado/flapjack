load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q = let val th = EVAL q in
 (print (label ^ "="); print_term (rconc th); print "\n") end;
print_eval "pv_source_terminal" ``MAP SND (SND (SND (parmove$pmov (([],[],[(SOME 7,NONE)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
print_eval "pv_source_self" ``MAP SND (SND (SND (parmove$pmov (([(SOME 1,SOME 1)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
print_eval "pv_source_chain" ``MAP SND (SND (SND (parmove$pmov (([(SOME 1,SOME 2);(SOME 2,SOME 3)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
print_eval "pv_source_cycle" ``MAP SND (SND (SND (parmove$pmov (([(SOME 1,SOME 2);(SOME 2,SOME 1)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
print_eval "pv_source_scratch" ``MAP SND (SND (SND (parmove$pmov (([(NONE,SOME 2);(SOME 1,NONE)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
print_eval "pv_source_duplicate" ``MAP SND (SND (SND (parmove$pmov (([(SOME 1,SOME 2);(SOME 1,SOME 3)],[],[]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
print_eval "pv_source_active" ``MAP SND (SND (SND (parmove$pmov (([],[(SOME 1,SOME 2);(SOME 2,NONE)],[(NONE,SOME 1)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
print_eval "pv_source_history" ``MAP SND (SND (SND (parmove$pmov (([],[],[(NONE,SOME 9)]) : (num option # num option) list # (num option # num option) list # (num option # num option) list))))``;
