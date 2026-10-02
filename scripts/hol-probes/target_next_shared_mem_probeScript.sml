load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp next_interference_SharedMem) then
 (print "next_shared_mem_full_statement="; print_term(concl next_interference_SharedMem); print "\n")
 else raise Fail "shared mem hypotheses";
val _ = OS.Process.exit OS.Process.success;
