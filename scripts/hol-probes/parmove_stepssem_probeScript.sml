load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q = let val th = EVAL q in
 (print (label ^ "="); print_term (rconc th); print "\n") end;
val env = ``\x:num option. case x of NONE => 99n | SOME k => 10*k+7``;
print_eval "pv_rtc_0_1" ``parmove$sem ([],[(SOME 1,SOME 2);(SOME 2,SOME 1)],[]) ^env (SOME 1)``;
print_eval "pv_rtc_0_2" ``parmove$sem ([],[(SOME 1,SOME 2);(SOME 2,SOME 1)],[]) ^env (SOME 2)``;
print_eval "pv_rtc_0_temp" ``parmove$sem ([],[(SOME 1,SOME 2);(SOME 2,SOME 1)],[]) ^env (NONE)``;
print_eval "pv_rtc_1_1" ``parmove$sem ([],[(SOME 1,SOME 2);(SOME 2,NONE)],[(NONE,SOME 1)]) ^env (SOME 1)``;
print_eval "pv_rtc_1_2" ``parmove$sem ([],[(SOME 1,SOME 2);(SOME 2,NONE)],[(NONE,SOME 1)]) ^env (SOME 2)``;
print_eval "pv_rtc_1_temp" ``parmove$sem ([],[(SOME 1,SOME 2);(SOME 2,NONE)],[(NONE,SOME 1)]) ^env (NONE)``;
print_eval "pv_rtc_2_1" ``parmove$sem ([],[(SOME 2,NONE)],[(SOME 1,SOME 2);(NONE,SOME 1)]) ^env (SOME 1)``;
print_eval "pv_rtc_2_2" ``parmove$sem ([],[(SOME 2,NONE)],[(SOME 1,SOME 2);(NONE,SOME 1)]) ^env (SOME 2)``;
print_eval "pv_rtc_2_temp" ``parmove$sem ([],[(SOME 2,NONE)],[(SOME 1,SOME 2);(NONE,SOME 1)]) ^env (NONE)``;
print_eval "pv_rtc_3_1" ``parmove$sem ([],[],[(SOME 2,NONE);(SOME 1,SOME 2);(NONE,SOME 1)]) ^env (SOME 1)``;
print_eval "pv_rtc_3_2" ``parmove$sem ([],[],[(SOME 2,NONE);(SOME 1,SOME 2);(NONE,SOME 1)]) ^env (SOME 2)``;
print_eval "pv_rtc_3_temp" ``parmove$sem ([],[],[(SOME 2,NONE);(SOME 1,SOME 2);(NONE,SOME 1)]) ^env (NONE)``;
