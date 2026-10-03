load "preamble";
load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble stack_removeProofTheory stack_removeTheory stackPropsTheory stackSemTheory stackLangTheory;
val _ = Globals.linewidth := 20000;
val clock_neutral_store_list_code = GEN_ALL(prove(``!xs n k. clock_neutral (store_list_code n k xs)``,
  Induct \\ fs [clock_neutral_def,store_list_code_def]
  \\ Cases \\ fs [clock_neutral_def,store_list_code_def,list_Seq_def]));
val _ = print ("store_list_neutral_statement=" ^ term_to_string(concl clock_neutral_store_list_code) ^ "\n");
val _ = print ("store_list_neutral_hypotheses=" ^ Int.toString(length(hyp clock_neutral_store_list_code)) ^ "\n");
val _ = print ("store_list_neutral_proved=" ^ "T" ^ "\n");
val evaluate_init_code_clock = GEN_ALL(prove(``evaluate (init_code gen_gc max_heap k,s) = (res,t) ==>
    evaluate (init_code gen_gc max_heap k,s with clock := c) =
      (res,t with clock := c)``,
  srw_tac[][] \\ match_mp_tac evaluate_clock_neutral \\ fs []
  \\ fs [clock_neutral_def,init_code_def] \\ rw []
  \\ fs [clock_neutral_def,init_code_def,halt_inst_def,
         list_Seq_def,init_memory_def,clock_neutral_store_list_code]));
val _ = print ("init_clock_statement=" ^ term_to_string(concl evaluate_init_code_clock) ^ "\n");
val _ = print ("init_clock_hypotheses=" ^ Int.toString(length(hyp evaluate_init_code_clock)) ^ "\n");
val _ = print ("init_clock_proved=" ^ "T" ^ "\n");
