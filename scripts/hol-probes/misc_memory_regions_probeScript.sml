load "preamble";
load "miscTheory";
open HolKernel Parse preamble miscTheory;
val _ = if null(hyp bytes_in_memory_APPEND) then
 (print "memory_append_full_statement="; print_term(concl bytes_in_memory_APPEND); print "\n")
 else raise Fail "append hypotheses";
val _ = if null(hyp bytes_in_memory_change_mem) then
 (print "memory_change_full_statement="; print_term(concl bytes_in_memory_change_mem); print "\n")
 else raise Fail "change hypotheses";
val _ = OS.Process.exit OS.Process.success;
