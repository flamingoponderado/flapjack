load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib wordPropsTheory wordSemTheory;
val _ = Globals.linewidth := 1000000;
val original = alloc_const;
val replay = GEN_ALL(prove(concl original,
  rpt strip_tac >>
  gvs[AllCaseEqs(),alloc_def] >>
  imp_res_tac pop_env_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac gc_const >> full_simp_tac(srw_ss())[]));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then () else raise Fail "open allocation invariant";
val _ = if aconv (concl replay) (concl(GEN_ALL original)) then () else raise Fail "statement drift";
val _ = (print "alloc_const_statement="; print_term(concl replay));
val _ = print("alloc_const_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("alloc_const_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
