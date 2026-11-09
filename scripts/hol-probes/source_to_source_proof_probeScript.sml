load "source_to_sourceProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "compile_semantics=" source_to_sourceProofTheory.compile_semantics;
val _ = show_thm "compile_semantics_oracle=" source_to_sourceProofTheory.compile_semantics_oracle;
val _ = show_thm "compile_definition=" source_to_sourceTheory.compile_def;
val _ = (print "compile_type="; print_type (type_of ``source_to_source$compile``); print "\n");
