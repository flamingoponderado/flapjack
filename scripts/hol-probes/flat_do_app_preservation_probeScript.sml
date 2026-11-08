load "flatSemTheory"; load "flatPropsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "do_app_const_typed=" flatSemTheory.do_app_const;
val _ = show_thm "do_app_state_unchanged_typed=" flatPropsTheory.do_app_state_unchanged;
