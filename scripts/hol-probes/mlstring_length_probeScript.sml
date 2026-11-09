load "mlstringTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "strlen=" mlstringTheory.strlen_def;
val _ = show "length_explode=" mlstringTheory.LENGTH_explode;
