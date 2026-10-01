load "bossLib";
load "preamble";
load "parmoveTheory";
open bossLib HolKernel Parse preamble parmoveTheory;
fun observe label term =
  let val th = EVAL term in
    print (label ^ "="); print_term (rhs (concl th)); print "\n"
  end;
val _ = observe "nt_empty" ``not_use_temp_before_assign ([] : (num option # num option) list)``;
val _ = observe "nt_read" ``not_use_temp_before_assign ([(SOME 1,NONE)] : (num option # num option) list)``;
val _ = observe "nt_both_none" ``not_use_temp_before_assign ([(NONE,NONE)] : (num option # num option) list)``;
val _ = observe "nt_write_stops" ``not_use_temp_before_assign ([(NONE,SOME 1);(SOME 2,NONE)] : (num option # num option) list)``;
val _ = observe "nt_recursive_read" ``not_use_temp_before_assign ([(SOME 1,SOME 2);(SOME 3,NONE)] : (num option # num option) list)``;
val _ = observe "nt_recursive_write" ``not_use_temp_before_assign ([(SOME 1,SOME 2);(NONE,SOME 3);(SOME 4,NONE)] : (num option # num option) list)``;
val _ = observe "nt_write" ``not_use_temp_before_assign ([(NONE,SOME 1)] : (num option # num option) list)``;
val _ = observe "nt_real_chain" ``not_use_temp_before_assign ([(SOME 1,SOME 2);(SOME 2,SOME 3)] : (num option # num option) list)``;
