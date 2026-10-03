load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory stack_to_labTheory
 stack_allocTheory stack_allocProofTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val NOT_bad_fun_return_IMP_SOME = prove (``  ¬bad_fun_return q ⇒ ∃n. q = SOME n``,
  Cases_on ‘q’ \\ simp []
);
val no_ret_correct_replay = prove (``   ∀t p y z cs bs. FST(SND(flatten t p y z cs bs)) ⇒ ∀s. IS_SOME (FST (evaluate (p,s)))``,
  ho_match_mp_tac flatten_ind >> rw[] >>
  pop_assum mp_tac \\
  Cases_on`p`>>simp[Once flatten_def,stackSemTheory.evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[IS_SOME_EXISTS] >>
  TRY pairarg_tac >> full_simp_tac(srw_ss())[] >>
  TRY pairarg_tac >> fs[] >> rw[stackSemTheory.evaluate_def] >>
  TRY pairarg_tac >> fs[] >> rw[] >> fs[stackSemTheory.evaluate_def] >>
  imp_res_tac NOT_bad_fun_return_IMP_SOME >>
  fs[EVAL ``flatten t Skip m n``] >>
  every_case_tac >> fs[] >>
  METIS_TAC[NOT_SOME_NONE,FST,option_CASES]
);
val th = DB.fetch "stack_to_labProof" "no_ret_correct";
val _ = show_types := true;
val _ = print "no_ret_correct=";
val _ = print_term (concl th);
val _ = print "\n";
val _ = print "no_ret_correct_types=";
val _ = app (fn v => print (term_to_string v ^ ":" ^ type_to_string (type_of v) ^ ";")) (fst (strip_forall (concl th)) @ free_vars (concl th));
val _ = print "\n";
val _ = print ("no_ret_correct_hypotheses=" ^ Int.toString (length (hyp th)) ^ "\n");
val _ = show_types := false;
val _ = print "no_ret_correct_proved=";
val _ = print_term (rhs (concl (EQT_INTRO (prove (concl th, ACCEPT_TAC no_ret_correct_replay)))));
val _ = print "\n";
val _ = print "stack_regs_type="; val _ = print (type_to_string (type_of ``\(s:('a,'c,'ffi) stackSem$state). s.regs``)); val _ = print "\n";
val _ = print "stack_fp_regs_type="; val _ = print (type_to_string (type_of ``\(s:('a,'c,'ffi) stackSem$state). s.fp_regs``)); val _ = print "\n";
val _ = print "stack_store_type="; val _ = print (type_to_string (type_of ``\(s:('a,'c,'ffi) stackSem$state). s.store``)); val _ = print "\n";
val _ = print "stack_code_type="; val _ = print (type_to_string (type_of ``\(s:('a,'c,'ffi) stackSem$state). s.code``)); val _ = print "\n";
