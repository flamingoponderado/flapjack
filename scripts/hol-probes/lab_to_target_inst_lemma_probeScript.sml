load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse preamble lab_to_targetProofTheory;
val _ = Globals.max_print_depth := 1000;
fun emit label th = if null(hyp th) then
 (print(label ^ "="); print_term(concl th); print "\n")
 else raise Fail(label ^ " has hypotheses");
fun emit_types label th =
 (show_types := true; emit label th; show_types := false);
val _ = emit "Inst_lemma" Inst_lemma;
val _ = emit_types "Inst_lemma_types" Inst_lemma;
val _ = OS.Process.exit OS.Process.success;
