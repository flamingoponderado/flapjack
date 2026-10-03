load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory;
val _ = Globals.linewidth := 1000000;
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported originals of stack_to_labProofScript.sml:3056-3104. *)
val _ = checked "full_make_init_def_statement" stack_to_labProofTheory.full_make_init_def;
val _ = checked "full_make_init_buffer_statement" stack_to_labProofTheory.full_make_init_buffer;
val _ = checked "full_make_init_ffi_statement" stack_to_labProofTheory.full_make_init_ffi;
val _ = checked "full_make_init_compile_statement" stack_to_labProofTheory.full_make_init_compile;
