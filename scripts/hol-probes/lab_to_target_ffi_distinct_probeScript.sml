(* Full original unconditional FFI-name distinctness capture. *)
load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open HolKernel Parse bossLib;
val _ = set_trace "types" 1;
val th = DB.fetch "lab_to_targetProof" "find_ffi_names_ALL_DISTINCT";
val _ = print "find_ffi_names_ALL_DISTINCT_statement_typed=";
val _ = print_term (concl th);
val _ = print "\n";
val _ = print "find_ffi_names_ALL_DISTINCT_hyp_count=";
val _ = print (Int.toString (length (hyp th)));
val _ = print "\n";
val _ = print "find_ffi_names_definition_typed=";
val _ = print_term (concl (DB.fetch "lab_to_target" "find_ffi_names_def"));
val _ = print "\n";
