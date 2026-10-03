load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib wordPropsTheory wordSemTheory;
val _ = Globals.linewidth := 1000000;
val original = GEN_ALL pop_env_const;
val replay = GEN_ALL(prove(concl original,
   srw_tac[][pop_env_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then () else raise Fail "open environment invariant";
val _ = if aconv (concl replay) (concl original) then () else raise Fail "statement drift";
val _ = (print "pop_env_const_statement="; print_term(concl replay));
val _ = print("pop_env_const_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("pop_env_const_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
