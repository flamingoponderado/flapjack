load "dataPropsTheory";
open HolKernel Parse boolLib bossLib;
val _ = (print "get_code_labels_def="; print_thm dataPropsTheory.get_code_labels_def; print "\n");
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = if null (hyp dataPropsTheory.get_code_labels_mk_ticks) then
  (print "get_code_labels_mk_ticks_typed=";
   print_term (concl dataPropsTheory.get_code_labels_mk_ticks); print "\n")
  else raise Fail "get_code_labels_mk_ticks has hypotheses";
