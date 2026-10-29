load "evaluatePropsTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "evaluate_decs_cons=" evaluatePropsTheory.evaluate_decs_cons;
val _ = show_thm "evaluate_decs_append=" evaluatePropsTheory.evaluate_decs_append;
