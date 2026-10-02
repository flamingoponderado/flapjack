load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp next_interference_ExtCall) then
 (print "next_extcall_full_statement="; print_term(concl next_interference_ExtCall); print "\n")
 else raise Fail "next_interference_ExtCall hypotheses";
val _ = if null(hyp next_interference_ccache) then
 (print "next_cache_full_statement="; print_term(concl next_interference_ccache); print "\n")
 else raise Fail "next_interference_ccache hypotheses";
val _ = OS.Process.exit OS.Process.success;
