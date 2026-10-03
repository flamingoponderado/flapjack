load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory;
val _ = Globals.linewidth := 1000000;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported originals of stack_to_labProofScript.sml:2741-3025. *)
val _ = checked "flatten_call_correct_statement" (GEN_ALL flatten_call_correct);
val _ = checked "halt_assum_def_statement" halt_assum_def;
val _ = checked "flatten_semantics_statement" (GEN_ALL flatten_semantics);
