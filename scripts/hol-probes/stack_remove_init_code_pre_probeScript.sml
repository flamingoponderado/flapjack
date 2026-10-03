load "preamble";
load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory stack_removeTheory stackSemTheory stackLangTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("init_code_pre_definition=" ^ term_to_string(concl init_code_pre_def) ^ "\n");
val _ = print ("init_code_pre_type=" ^ type_to_string(type_of ``init_code_pre``) ^ "\n");
val _ = print ("init_code_pre_hypotheses=" ^ Int.toString(length(hyp init_code_pre_def)) ^ "\n");
