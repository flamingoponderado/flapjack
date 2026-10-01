load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun observe label term = let val th = EVAL term in print(label ^ "="); print_term(rhs(concl th)); print "\n" end;
val _ = observe "ntm_real" ``not_use_temp_before_assign ([(SOME T,SOME 7)] : (bool option # num option) list)``;
val _ = observe "ntm_read" ``not_use_temp_before_assign ([(SOME F,NONE)] : (bool option # num option) list)``;
val _ = observe "ntm_write" ``not_use_temp_before_assign ([(NONE,SOME 7);(SOME T,NONE)] : (bool option # num option) list)``;
val _ = observe "ntm_both" ``not_use_temp_before_assign ([(NONE,NONE)] : (bool option # num option) list)``;
