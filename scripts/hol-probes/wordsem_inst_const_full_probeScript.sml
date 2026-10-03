load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib wordPropsTheory
  wordSemTheory wordLangTheory wordConvsTheory miscTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val original = GEN_ALL inst_const_full;
val replay = GEN_ALL(prove(concl original,
  rw[inst_def]>>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  rpt (pairarg_tac >> fs []) >>
  imp_res_tac assign_const_full >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac mem_store_const >> full_simp_tac(srw_ss())[] >> srw_tac[][]));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then ()
  else raise Fail "open instruction invariant";
val _ = if aconv (concl replay) (concl original) then () else raise Fail "statement drift";
val _ = (print "inst_const_full_statement="; print_term(concl replay));
val _ = print("inst_const_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("inst_const_full_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
