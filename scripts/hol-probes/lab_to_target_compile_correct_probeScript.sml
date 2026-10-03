load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse preamble labSemTheory lab_to_targetProofTheory;
val _ = Globals.max_print_depth := 1000;
fun emit label th = if null(hyp th) then
 (print(label ^ "="); print_term(concl th); print "\n")
 else raise Fail(label ^ " has hypotheses");
fun emit_types label th =
 (show_types := true; emit label th; show_types := false);
val _ = emit "compile_correct" compile_correct;
val _ = emit_types "compile_correct_types" compile_correct;
(* The induction principle whose per-call hypotheses are the case IHs. *)
val _ = emit "lab_evaluate_ind" labSemTheory.evaluate_ind;
val _ = OS.Process.exit OS.Process.success;
