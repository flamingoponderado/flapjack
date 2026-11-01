load "bvi_to_dataProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "v_to_bytes_eq=" bvi_to_dataProofTheory.v_to_bytes_eq;
val _ = show "v_to_words_eq=" bvi_to_dataProofTheory.v_to_words_eq;
