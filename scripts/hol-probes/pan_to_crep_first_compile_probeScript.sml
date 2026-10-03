load "bossLib";
load "preamble";
load "pan_to_crepProofTheory";
open bossLib HolKernel Parse preamble pan_to_crepProofTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "=");print_term(concl th);print "\n");
val _ = capture "first_compile_prog_all_distinct" (DB.fetch "pan_to_crepProof" "first_compile_prog_all_distinct");
