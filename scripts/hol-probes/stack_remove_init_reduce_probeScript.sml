load "preamble";
load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory stack_removeTheory stackLangTheory stackSemTheory wordSemTheory;
val _ = Globals.linewidth := 20000;
val full_stack_space = GEN_ALL(prove(``(init_reduce gen_gc jump off k code bitmaps data_sp coracle s8).stack_space <=
    LENGTH (init_reduce gen_gc jump off k code bitmaps data_sp coracle s8).stack``,
  fs [init_reduce_def,LENGTH_read_mem]));
val _ = print ("init_reduce_definition=" ^ term_to_string(concl init_reduce_def) ^ "\n");
val _ = print ("init_reduce_type=" ^ type_to_string(type_of ``init_reduce``) ^ "\n");
val _ = print ("init_reduce_hypotheses=" ^ Int.toString(length(hyp init_reduce_def)) ^ "\n");
val _ = print ("init_reduce_stack_space_statement=" ^ term_to_string(concl full_stack_space) ^ "\n");
val _ = print ("init_reduce_stack_space_hypotheses=" ^ Int.toString(length(hyp full_stack_space)) ^ "\n");
val _ = print ("init_reduce_stack_space_proved=T\n");
