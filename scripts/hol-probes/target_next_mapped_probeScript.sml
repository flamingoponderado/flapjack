load "preamble";
load "targetPropsTheory";
open HolKernel Parse preamble targetPropsTheory;
val _ = if null(hyp next_interference_MappedRead) then
 (print "next_mapped_read_full_statement="; print_term(concl next_interference_MappedRead); print "\n")
 else raise Fail "next_interference_MappedRead hypotheses";
val _ = if null(hyp next_interference_MappedWrite) then
 (print "next_mapped_write_full_statement="; print_term(concl next_interference_MappedWrite); print "\n")
 else raise Fail "next_interference_MappedWrite hypotheses";
val _ = OS.Process.exit OS.Process.success;
