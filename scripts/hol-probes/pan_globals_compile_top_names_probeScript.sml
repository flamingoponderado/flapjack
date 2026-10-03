load "bossLib";
load "preamble";
load "pan_globalsProofTheory";
open bossLib HolKernel Parse preamble pan_globalsProofTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "=");print_term(concl th);print "\n");
val _ = capture "ALL_DISTINCT_compile_top" (DB.fetch "pan_globalsProof" "ALL_DISTINCT_compile_top");
