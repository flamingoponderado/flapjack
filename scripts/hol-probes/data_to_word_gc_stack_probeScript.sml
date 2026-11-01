load "data_to_word_gcProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show label th =
  if null (hyp th) then
    (print label; print "="; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "stack_rel_typed" data_to_word_gcProofTheory.stack_rel_def;
val _ = show "the_global_typed" data_to_word_gcProofTheory.the_global_def;
val _ = show "contains_loc_typed" data_to_word_gcProofTheory.contains_loc_def;
