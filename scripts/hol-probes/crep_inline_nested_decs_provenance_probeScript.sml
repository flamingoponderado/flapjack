load "preamble";
load "crep_inlineProofTheory";
open HolKernel Parse bossLib preamble crep_inlineProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val full = GEN_ALL exps_of_nested_decs;
val _ = if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
val _ = print("nested_decs_provenance=" ^ term_to_string(concl full) ^ "\n");
