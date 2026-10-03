load "preamble";
load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory stack_removeTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("init_limits_double_definition=" ^ term_to_string(concl get_stack_heap_limit''_def) ^ "\n");
val _ = print ("init_limits_double_type=" ^ type_to_string(type_of ``get_stack_heap_limit''``) ^ "\n");
val _ = print ("init_limits_double_hypotheses=" ^ Int.toString(length(hyp get_stack_heap_limit''_def)) ^ "\n");
val _ = print ("init_limits_double_store_count=" ^ term_to_string(rhs(concl(EVAL ``LENGTH store_list``))) ^ "\n");
