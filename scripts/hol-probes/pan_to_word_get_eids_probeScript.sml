load "bossLib";
load "preamble";
load "pan_to_wordProofTheory";
open bossLib HolKernel Parse preamble pan_to_wordProofTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "=");print_term(concl th);print "\n");
val _ = capture "get_eids_pan_simp_compile_eq" (DB.fetch "pan_to_wordProof" "get_eids_pan_simp_compile_eq");
val _ = capture "FDOM_get_eids_pan_globals_compile_eq" (DB.fetch "pan_to_wordProof" "FDOM_get_eids_pan_globals_compile_eq");
val _ = capture "size_of_eids_compile_top" (DB.fetch "pan_to_wordProof" "size_of_eids_compile_top");
