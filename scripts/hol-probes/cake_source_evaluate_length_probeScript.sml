load "evaluatePropsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "evaluate_length_typed=" evaluatePropsTheory.evaluate_length;
val _ = show_thm "evaluate_sing_typed=" evaluatePropsTheory.evaluate_sing;
