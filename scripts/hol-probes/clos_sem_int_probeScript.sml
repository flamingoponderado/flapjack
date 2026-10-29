load "closSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "int_app_typed=" closSemTheory.do_int_app_def;
val _ = show_eval "div_negative_left=" ``closSem$do_int_app Div [Number (-7); Number 3]``;
val _ = show_eval "div_negative_right=" ``closSem$do_int_app Div [Number 7; Number (-3)]``;
val _ = show_eval "mod_negative_left=" ``closSem$do_int_app Mod [Number (-7); Number 3]``;
val _ = show_eval "mod_negative_right=" ``closSem$do_int_app Mod [Number 7; Number (-3)]``;
val _ = show_eval "divide_zero=" ``closSem$do_int_app Div [Number 7; Number 0]``;
val _ = show_eval "small_upper=" ``closSem$do_int_app (LessConstSmall 999999) [Number 1000000]``;
val _ = show_eval "small_invalid=" ``closSem$do_int_app (LessConstSmall 1000000) [Number 0]``;
