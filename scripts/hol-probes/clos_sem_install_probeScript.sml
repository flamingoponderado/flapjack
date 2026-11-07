load "closSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "bytes_typed=" closSemTheory.v_to_bytes_def;
val _ = show_thm "words_typed=" closSemTheory.v_to_words_def;
val _ = show_thm "install_typed=" closSemTheory.do_install_def;
val _ = show_thm "clock_typed=" closSemTheory.do_install_clock;
val _ = show_thm "clock_bound_typed=" closSemTheory.do_install_clock_less_eq;
val _ = show_eval "wrong_arity=" ``FST (closSem$do_install [] (ARB : (unit,unit) closSem$state))``;
val _ = show_eval "one_arg=" ``FST (closSem$do_install [Number 0] (ARB : (unit,unit) closSem$state))``;
