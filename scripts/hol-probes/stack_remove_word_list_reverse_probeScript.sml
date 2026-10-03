load "preamble"; load "helperLib"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib stack_removeProofTheory
 stack_removeTheory stackLangTheory stackSemTheory stackPropsTheory set_sepTheory
 miscTheory wordsTheory listTheory addressTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val original = prove(``!xs a. word_list a xs =
  word_list_rev (a + n2w (LENGTH xs) * bytes_in_word) (REVERSE xs)``,
  recInduct SNOC_INDUCT >> fs [REVERSE_SNOC]
  >> fs [SNOC_APPEND,word_list_APPEND,word_list_rev_def,word_list_def]
  >> rw [SEP_CLAUSES,ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  >> fs [AC STAR_COMM STAR_ASSOC]);
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = (print "word_list_reverse_statement="; print_term(concl original); print "\n");
val _ = print("word_list_reverse_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
val _ = print("word_list_reverse_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
