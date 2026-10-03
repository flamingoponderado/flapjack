load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib wordPropsTheory wordSemTheory;
val _ = Globals.linewidth := 1000000;
val original = gc_const;
val replay = GEN_ALL(prove(concl original,
  simp[gc_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> srw_tac[][]));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then () else raise Fail "open GC invariant";
val _ = if aconv (concl replay) (concl(GEN_ALL original)) then () else raise Fail "statement drift";
val _ = (print "gc_const_statement="; print_term(concl replay));
val _ = print("gc_const_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("gc_const_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
