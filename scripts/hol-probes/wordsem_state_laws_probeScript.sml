load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib wordPropsTheory wordSemTheory;
val _ = Globals.linewidth := 1000000;
fun check name th original =
  if null(hyp th) andalso null(free_vars(concl th)) andalso aconv (concl th) (concl(GEN_ALL original))
  then () else raise Fail ("replay " ^ name);
val mem_list_rearrange_replay = GEN_ALL(prove(concl mem_list_rearrange,
  full_simp_tac(srw_ss())[MEM_EL]>>srw_tac[][wordSemTheory.list_rearrange_def]>>
  imp_res_tac BIJ_IFF_INV>>
  full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF,SURJ_DEF]>>
  srw_tac[][EQ_IMP_THM]>>full_simp_tac(srw_ss())[EL_GENLIST]
  >- metis_tac[]>>
  qexists_tac `g n`>>full_simp_tac(srw_ss())[]));
val _ = check "mem_list_rearrange" mem_list_rearrange_replay mem_list_rearrange;
val _ = (print "mem_list_rearrange_statement="; print_term(concl mem_list_rearrange_replay); print "\n");
val _ = print("mem_list_rearrange_hypotheses=" ^ Int.toString(length(hyp mem_list_rearrange_replay)) ^ "\n");
val set_var_const_replay = GEN_ALL(prove(concl set_var_const,
  EVAL_TAC));
val _ = check "set_var_const" set_var_const_replay set_var_const;
val _ = (print "set_var_const_statement="; print_term(concl set_var_const_replay); print "\n");
val _ = print("set_var_const_hypotheses=" ^ Int.toString(length(hyp set_var_const_replay)) ^ "\n");
val set_var_with_const_replay = GEN_ALL(prove(concl set_var_with_const,
  EVAL_TAC));
val _ = check "set_var_with_const" set_var_with_const_replay set_var_with_const;
val _ = (print "set_var_with_const_statement="; print_term(concl set_var_with_const_replay); print "\n");
val _ = print("set_var_with_const_hypotheses=" ^ Int.toString(length(hyp set_var_with_const_replay)) ^ "\n");
val set_store_const_replay = GEN_ALL(prove(concl set_store_const,
  EVAL_TAC));
val _ = check "set_store_const" set_store_const_replay set_store_const;
val _ = (print "set_store_const_statement="; print_term(concl set_store_const_replay); print "\n");
val _ = print("set_store_const_hypotheses=" ^ Int.toString(length(hyp set_store_const_replay)) ^ "\n");
val get_var_set_var_replay = GEN_ALL(prove(concl get_var_set_var,
  simp[get_var_def,set_var_def,lookup_insert]));
val _ = check "get_var_set_var" get_var_set_var_replay get_var_set_var;
val _ = (print "get_var_set_var_statement="; print_term(concl get_var_set_var_replay); print "\n");
val _ = print("get_var_set_var_hypotheses=" ^ Int.toString(length(hyp get_var_set_var_replay)) ^ "\n");
val get_vars_length_lemma_replay = GEN_ALL(prove(concl get_vars_length_lemma,
  Induct>>full_simp_tac(srw_ss())[get_vars_def]>>
  Cases_on`get_var h s`>>full_simp_tac(srw_ss())[]>>
  Cases_on`get_vars ls s`>>full_simp_tac(srw_ss())[]>>
  metis_tac[LENGTH]));
val _ = check "get_vars_length_lemma" get_vars_length_lemma_replay get_vars_length_lemma;
val _ = (print "get_vars_length_lemma_statement="; print_term(concl get_vars_length_lemma_replay); print "\n");
val _ = print("get_vars_length_lemma_hypotheses=" ^ Int.toString(length(hyp get_vars_length_lemma_replay)) ^ "\n");
val stack_size_eq_replay = GEN_ALL(prove(concl stack_size_eq,
  rw[stack_size_def,stack_size_frame_def]));
val _ = check "stack_size_eq" stack_size_eq_replay stack_size_eq;
val _ = (print "stack_size_eq_statement="; print_term(concl stack_size_eq_replay); print "\n");
val _ = print("stack_size_eq_hypotheses=" ^ Int.toString(length(hyp stack_size_eq_replay)) ^ "\n");
val stack_size_eq2_replay = GEN_ALL(prove(concl stack_size_eq2,
  rw[stack_size_def,stack_size_frame_def]));
val _ = check "stack_size_eq2" stack_size_eq2_replay stack_size_eq2;
val _ = (print "stack_size_eq2_statement="; print_term(concl stack_size_eq2_replay); print "\n");
val _ = print("stack_size_eq2_hypotheses=" ^ Int.toString(length(hyp stack_size_eq2_replay)) ^ "\n");
val s_key_eq_def2_replay = GEN_ALL(prove(concl s_key_eq_def2,
  recInduct s_key_eq_ind >> simp[s_key_eq_def] >>
  rpt strip_tac >> irule CONJ_COMM));
val _ = check "s_key_eq_def2" s_key_eq_def2_replay s_key_eq_def2;
val _ = (print "s_key_eq_def2_statement="; print_term(concl s_key_eq_def2_replay); print "\n");
val _ = print("s_key_eq_def2_hypotheses=" ^ Int.toString(length(hyp s_key_eq_def2_replay)) ^ "\n");
val lastn_stack_size_some_replay = GEN_ALL(prove(concl LASTN_stack_size_SOME,
  Induct_on `stack` >> rw[LASTN_ALT,stack_size_eq] >>
  fs[stack_size_eq2] >>
  res_tac >>
  goal_assum drule >>
  intLib.COOPER_TAC));
val _ = check "LASTN_stack_size_SOME" lastn_stack_size_some_replay LASTN_stack_size_SOME;
val _ = (print "LASTN_stack_size_SOME_statement="; print_term(concl lastn_stack_size_some_replay); print "\n");
val _ = print("LASTN_stack_size_SOME_hypotheses=" ^ Int.toString(length(hyp lastn_stack_size_some_replay)) ^ "\n");
