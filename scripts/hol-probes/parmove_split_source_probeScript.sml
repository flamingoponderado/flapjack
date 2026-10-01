load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun print_eval label q = let val th = EVAL q in
 (print (label ^ "="); print_term (rconc th); print "\n") end;
print_eval "pv_split_empty" ``splitAtPki (\i p. SND p = (SOME 1 : num option)) (\before after. (before,after)) ([] : (num option # num option) list)``;
print_eval "pv_split_first" ``splitAtPki (\i p. SND p = (SOME 1 : num option)) (\before after. (before,after)) ([(SOME 7,SOME 1);(SOME 8,SOME 1)] : (num option # num option) list)``;
print_eval "pv_split_middle" ``splitAtPki (\i p. SND p = (SOME 1 : num option)) (\before after. (before,after)) ([(SOME 7,SOME 2);(SOME 8,SOME 1);(SOME 9,SOME 1)] : (num option # num option) list)``;
print_eval "pv_split_absent" ``splitAtPki (\i p. SND p = (SOME 1 : num option)) (\before after. (before,after)) ([(SOME 7,SOME 2);(SOME 8,SOME 3)] : (num option # num option) list)``;
print_eval "pv_split_none" ``splitAtPki (\i p. SND p = (NONE : num option)) (\before after. (before,after)) ([(SOME 7,SOME 2);(SOME 8,NONE);(SOME 9,NONE)] : (num option # num option) list)``;
print_eval "pv_split_duplicate_dest" ``splitAtPki (\i p. SND p = (SOME 1 : num option)) (\before after. (before,after)) ([(SOME 7,SOME 2);(SOME 7,SOME 1);(SOME 7,SOME 3)] : (num option # num option) list)``;
print_eval "pv_split_late_zero" ``splitAtPki (\i p. SND p = (SOME 0 : num option)) (\before after. (before,after)) ([(NONE,SOME 2);(SOME 0,SOME 0)] : (num option # num option) list)``;
