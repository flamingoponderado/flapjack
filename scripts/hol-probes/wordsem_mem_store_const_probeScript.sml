load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib wordPropsTheory wordSemTheory;
val _ = Globals.linewidth := 1000000;
val original = mem_store_const;
val replay = GEN_ALL(prove(concl original,
  EVAL_TAC >> srw_tac[][] >> srw_tac[][]));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then () else raise Fail "open memory-store invariant";
val _ = if aconv (concl replay) (concl(GEN_ALL original)) then () else raise Fail "statement drift";
val _ = (print "mem_store_const_statement="; print_term(concl replay));
val _ = print("mem_store_const_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("mem_store_const_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
