load "preamble";
load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("stack_heap_limit_definition=" ^ term_to_string(concl stack_heap_limit_ok_def) ^ "\n");
val _ = print ("stack_heap_limit_type=" ^ type_to_string(type_of ``stack_heap_limit_ok``) ^ "\n");
val _ = print ("stack_heap_limit_hypotheses=" ^ Int.toString(length(hyp stack_heap_limit_ok_def)) ^ "\n");
