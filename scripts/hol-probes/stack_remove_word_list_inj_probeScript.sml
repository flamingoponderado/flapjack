load "preamble"; load "helperLib"; load "stack_removeProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib stack_removeProofTheory
 stack_removeTheory stackLangTheory stackSemTheory stackPropsTheory set_sepTheory
 miscTheory wordsTheory listTheory addressTheory;
val _ = Globals.linewidth := 1000000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val original = prove(``∀xs a u u'. word_list a xs u ∧ word_list a xs u' ⇒ u = u'``,
Induct>>rw[miscTheory.word_list_def]>- gs[set_sepTheory.emp_def]>>
  first_x_assum $ qspecl_then [‘a+bytes_in_word’, ‘u DIFF {(a,h)}’, ‘u' DIFF {(a,h)}’] assume_tac>>
  fs [Once set_sepTheory.STAR_def,set_sepTheory.SPLIT_EQ,word_list_def]>>
  fs [Once set_sepTheory.STAR_def,set_sepTheory.SPLIT_EQ,word_list_def]>>
  fs [set_sepTheory.one_def] >> gs[]>>
  gs[DIFF_DEF,EXTENSION]>>metis_tac[]);
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = (print "word_list_inj_statement="; print_term(concl original); print "\n");
val _ = print("word_list_inj_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
val _ = print("word_list_inj_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
