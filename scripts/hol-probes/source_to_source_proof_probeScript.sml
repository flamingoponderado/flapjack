load "source_to_sourceProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "compile_semantics=" source_to_sourceProofTheory.compile_semantics;
val _ = show_thm "compile_semantics_oracle=" source_to_sourceProofTheory.compile_semantics_oracle;
