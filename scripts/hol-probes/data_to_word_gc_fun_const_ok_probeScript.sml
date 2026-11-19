load "preamble"; load "data_to_word_gcProofTheory";
open HolKernel Parse bossLib preamble data_to_word_gcProofTheory;
val _ = Globals.linewidth := 1000000;
fun pr_stmt label th = (print (label ^ "="); print_term (concl th); print "\n");
fun pr_hyps label th = (print (label ^ "="); print (Int.toString (length (hyp th))); print "\n");
fun pr_typed label th = (print (label ^ "="); Lib.with_flag (Globals.show_types, true) print_term (concl th); print "\n");
val _ = pr_stmt "gc_fun_const_ok_word_gc_fun_statement" gc_fun_const_ok_word_gc_fun;
val _ = pr_hyps "gc_fun_const_ok_word_gc_fun_hypotheses" gc_fun_const_ok_word_gc_fun;
val _ = pr_typed "gc_fun_const_ok_word_gc_fun_typed" gc_fun_const_ok_word_gc_fun;
val _ = pr_hyps "stack_rel_IMP_size_of_stack_hypotheses" stack_rel_IMP_size_of_stack;
val _ = pr_typed "stack_rel_IMP_size_of_stack_typed" stack_rel_IMP_size_of_stack;
val _ = pr_typed "code_rel_def_typed" code_rel_def;
val _ = pr_typed "code_oracle_rel_def_typed" code_oracle_rel_def;
val _ = pr_typed "state_rel_thm_typed" state_rel_thm;
val _ = pr_typed "state_rel_with_clock_typed" state_rel_with_clock;
val _ = pr_typed "state_rel_with_fp_regs_typed" state_rel_with_fp_regs;
val _ = pr_typed "dec_clock_inc_clock_typed" dec_clock_inc_clock;
val _ = pr_typed "state_rel_gc_gen_typed" state_rel_gc_gen;
val _ = pr_typed "PERM_toList_lookup_eq_typed" PERM_toList_lookup_eq;
val _ = pr_typed "PERM_toList_delete_typed" PERM_toList_delete;
val _ = pr_typed "get_vars_PERM_toList_inter_typed" get_vars_PERM_toList_inter;
val _ = pr_typed "LIST_REL_exists_witness_typed" LIST_REL_exists_witness;
val _ = pr_typed "size_of_heap_call_push_env_typed" size_of_heap_call_push_env;
val _ = pr_typed "option_le_OPTION_MAP2_MAX_typed" option_le_OPTION_MAP2_MAX;
val _ = pr_typed "bytes_in_word_ADD_1_NOT_ZERO_typed" bytes_in_word_ADD_1_NOT_ZERO;
val _ = pr_typed "w2n_minus_1_LESS_EQ_typed" w2n_minus_1_LESS_EQ;
val _ = pr_typed "get_var_inc_clock_typed" get_var_inc_clock;
val _ = pr_typed "get_vars_inc_clock_typed" get_vars_inc_clock;
val _ = pr_typed "set_var_inc_clock_typed" set_var_inc_clock;
(* The source theorem is local: replay its original statement and proof. *)
val stack_rel_imp_subset_replay = prove (
  ``∀xs ys. LIST_REL stack_rel xs ys ⇒
      set (wordSem$enc_stack ys) ⊆ set (MAP SND (flat xs ys))``,
  Induct \\ gvs [wordSemTheory.enc_stack_def,PULL_EXISTS]
  \\ Cases \\ Cases_on ‘y’ \\ gvs [stack_rel_def]
  \\ rw [] \\ rename [‘StackFrame opt l1 l2 han’]
  \\ Cases_on ‘han’ \\ TRY (PairCases_on ‘x’)
  \\ gvs [wordSemTheory.enc_stack_def,flat_def,stack_rel_def]
  \\ last_x_assum old_drule \\ strip_tac \\ gvs []
  \\ (qsuff_tac ‘set (MAP SND l2) ⊆ set (MAP SND (join_env s l2))’
      >- gvs [SUBSET_DEF])
  \\ gvs [SUBSET_DEF,join_env_def,MAP_MAP_o,o_DEF]
  \\ gvs [LAMBDA_PROD]
  \\ gvs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,EXISTS_PROD]
  \\ gvs [MEM_FILTER] \\ metis_tac []);
val _ = pr_typed "stack_rel_imp_subset_typed" stack_rel_imp_subset_replay;
val _ = pr_typed "mk_loc_def_typed" mk_loc_def;
val mkLocLhs = fst (dest_eq (concl mk_loc_def));
val _ = (print "mk_loc_function_type=";
  print (type_to_string (type_of (fst (dest_comb mkLocLhs)))); print "\n");
val _ = pr_typed "state_rel_get_var_IMP_typed" state_rel_get_var_IMP;
val _ = pr_typed "word_ml_inv_lookup_typed" word_ml_inv_lookup;
val _ = pr_typed "word_ml_inv_insert_typed" word_ml_inv_insert;
val _ = pr_typed "state_rel_get_vars_IMP_typed" state_rel_get_vars_IMP;
val _ = pr_typed "state_rel_cut_env_typed" state_rel_cut_env;
val _ = pr_typed "state_rel_cut_IMP_typed" state_rel_cut_IMP;
val _ = pr_typed "cut_env_IMP_cut_env_typed" cut_env_IMP_cut_env;
val _ = pr_typed "cut_env_IMP_cut_envs_typed" cut_env_IMP_cut_envs;
val _ = pr_typed "gc_add_call_env_typed" gc_add_call_env;
val _ = pr_typed "inter_union_lemma_typed" inter_union_lemma;
val _ = pr_typed "option_le_tl_typed" option_le_tl;
val _ = pr_typed "cut_env_adjust_sets_insert_ODD_typed" cut_env_adjust_sets_insert_ODD;
val _ = pr_typed "cut_locals_def_typed" cut_locals_def;
val _ = pr_typed "state_rel_cut_env_cut_env_typed" state_rel_cut_env_cut_env;
load "data_to_word_assignProofTheory";
open data_to_word_assignProofTheory;
val _ = pr_typed "state_rel_cut_state_opt_SOME_typed" state_rel_cut_state_opt_SOME;
val _ = pr_typed "cut_state_opt_SOME_eq_typed" cut_state_opt_SOME_eq;
val _ = pr_typed "state_rel_cut_state_opt_set_var_typed" state_rel_cut_state_opt_set_var;
val _ = pr_typed "cut_env_idempotent_typed" cut_env_idempotent;
val _ = pr_typed "cut_env_cut_env_list_insert_typed" cut_env_cut_env_list_insert;
val _ = pr_typed "sptree_list_insert_def_typed" sptreeTheory.list_insert_def;
val _ = pr_typed "join_env_submap_MEM_typed" join_env_submap_MEM;
val _ = pr_typed "state_rel_FLOOKUP_heap_typed" state_rel_FLOOKUP_heap;
val _ = pr_typed "evaluate_SilentFFI_3_typed" evaluate_SilentFFI_3;
val _ = pr_typed "cut_state_opt_IMP_cut_locals_typed" cut_state_opt_IMP_cut_locals;
val _ = pr_typed "state_rel_0_get_vars_IMP_typed" data_to_word_gcProofTheory.state_rel_0_get_vars_IMP;
val _ = pr_typed "get_var_T_OR_F_typed" data_to_word_gcProofTheory.get_var_T_OR_F;
val _ = pr_typed "get_var_isT_OR_isF_typed" data_to_word_gcProofTheory.get_var_isT_OR_isF;
val _ = pr_typed "state_rel_cut_state_opt_get_var_typed" data_to_word_gcProofTheory.state_rel_cut_state_opt_get_var;
val _ = pr_typed "set_vars_sing_typed" data_to_word_gcProofTheory.set_vars_sing;
val _ = pr_typed "jump_exc_call_env_typed" data_to_word_gcProofTheory.jump_exc_call_env;
val _ = pr_typed "jump_exc_dec_clock_typed" data_to_word_gcProofTheory.jump_exc_dec_clock;
val _ = pr_typed "jump_exc_push_env_NONE_typed" data_to_word_gcProofTheory.jump_exc_push_env_NONE;
val _ = pr_typed "option_le_stack_size_cons_typed" data_to_word_gcProofTheory.option_le_stack_size_cons;
val _ = pr_typed "option_le_stack_size_append_typed" data_to_word_gcProofTheory.option_le_stack_size_append;
val _ = pr_typed "inter_insert_union_typed" data_to_word_gcProofTheory.inter_insert_union;
val _ = pr_typed "state_rel_pop_env_IMP_typed" data_to_word_gcProofTheory.state_rel_pop_env_IMP;
val _ = pr_typed "state_rel_pop_env_set_var_IMP_typed" data_to_word_gcProofTheory.state_rel_pop_env_set_var_IMP;
val _ = pr_typed "BUTLASTN_APPEND_LASTN_typed" data_to_word_gcProofTheory.BUTLASTN_APPEND_LASTN;
val _ = pr_typed "LASTN_LIST_REL_LEMMA_typed" data_to_word_gcProofTheory.LASTN_LIST_REL_LEMMA;
val _ = pr_typed "LASTN_CONS_IMP_LENGTH_typed" data_to_word_gcProofTheory.LASTN_CONS_IMP_LENGTH;
val _ = pr_typed "LASTN_IMP_APPEND_typed" data_to_word_gcProofTheory.LASTN_IMP_APPEND;
val _ = pr_typed "state_rel_jump_exc_typed" data_to_word_gcProofTheory.state_rel_jump_exc;
val _ = pr_typed "get_vars_IMP_LENGTH_typed" data_to_word_gcProofTheory.get_vars_IMP_LENGTH;
val _ = pr_typed "get_vars_IMP_LENGTH_word_typed" data_to_word_gcProofTheory.get_vars_IMP_LENGTH_word;
val _ = pr_typed "lookup_adjust_var_fromList2_typed" data_to_word_gcProofTheory.lookup_adjust_var_fromList2;
val _ = pr_typed "state_rel_call_env_typed" data_to_word_gcProofTheory.state_rel_call_env;
val _ = pr_typed "word_ml_inv_CodePtr_typed" data_to_word_gcProofTheory.word_ml_inv_CodePtr;
val _ = pr_typed "state_rel_CodePtr_typed" data_to_word_gcProofTheory.state_rel_CodePtr;
val _ = pr_typed "data_get_vars_SNOC_IMP_typed" data_to_word_gcProofTheory.data_get_vars_SNOC_IMP;
val _ = pr_typed "word_get_vars_SNOC_IMP_typed" data_to_word_gcProofTheory.word_get_vars_SNOC_IMP;
val _ = pr_typed "find_code_thm_typed" data_to_word_gcProofTheory.find_code_thm;
val _ = pr_typed "cut_env_adjust_set_lookup_0_typed" data_to_word_gcProofTheory.cut_env_adjust_set_lookup_0;
val _ = pr_typed "cut_env_IMP_MEM_typed" data_to_word_gcProofTheory.cut_env_IMP_MEM;
val _ = pr_typed "cut_env_IMP_lookup_typed" data_to_word_gcProofTheory.cut_env_IMP_lookup;
val _ = pr_typed "cut_env_IMP_lookup_EQ_typed" data_to_word_gcProofTheory.cut_env_IMP_lookup_EQ;
val _ = pr_typed "cut_env_res_IS_SOME_IMP_typed" data_to_word_gcProofTheory.cut_env_res_IS_SOME_IMP;
val _ = pr_typed "adjust_var_cut_env_IMP_MEM_typed" data_to_word_gcProofTheory.adjust_var_cut_env_IMP_MEM;
val _ = pr_typed "NOT_0_domain_typed" data_to_word_gcProofTheory.NOT_0_domain;
val _ = pr_typed "cut_envs_SND_nonzero_typed" data_to_word_gcProofTheory.cut_envs_SND_nonzero;
val _ = pr_typed "lookup_adjust_var_after_cut_typed" data_to_word_gcProofTheory.lookup_adjust_var_after_cut;
val _ = pr_typed "state_rel_call_env_push_opt_typed" data_to_word_gcProofTheory.state_rel_call_env_push_opt;
val _ = pr_typed "state_rel_call_env_push_typed" data_to_word_gcProofTheory.state_rel_call_env_push;
val _ = pr_typed "state_rel_call_env_push_env_typed" data_to_word_gcProofTheory.state_rel_call_env_push_env;
val _ = pr_typed "find_code_thm_ret_typed" data_to_word_gcProofTheory.find_code_thm_ret;
val _ = pr_typed "find_code_thm_handler_typed" data_to_word_gcProofTheory.find_code_thm_handler;
val _ = pr_typed "bad_dest_args_def_polymorphic_typed" wordSemTheory.bad_dest_args_def;
val _ = pr_typed "data_find_code_typed" data_to_word_gcProofTheory.data_find_code;
val _ = pr_typed "gc_s_key_eq_LENGTH_typed" data_to_word_gcProofTheory.s_key_eq_LENGTH;
val _ = pr_typed "gc_s_key_eq_LASTN_typed" data_to_word_gcProofTheory.s_key_eq_LASTN;
val _ = pr_typed "evaluate_mk_loc_EQ_typed" data_to_word_gcProofTheory.evaluate_mk_loc_EQ;
val _ = pr_typed "mk_loc_eq_push_env_exc_Exception_typed" data_to_word_gcProofTheory.mk_loc_eq_push_env_exc_Exception;
val _ = pr_typed "evaluate_IMP_domain_EQ_typed" data_to_word_gcProofTheory.evaluate_IMP_domain_EQ;
val _ = pr_typed "evaluate_IMP_domain_EQ_Exc_typed" data_to_word_gcProofTheory.evaluate_IMP_domain_EQ_Exc;
val _ = pr_typed "mk_loc_jump_exc_typed" data_to_word_gcProofTheory.mk_loc_jump_exc;
val _ = pr_typed "gc_inc_clock_def_typed" data_to_word_gcProofTheory.inc_clock_def;
val _ = pr_typed "gc_inc_clock_0_typed" data_to_word_gcProofTheory.inc_clock_0;
val _ = pr_typed "gc_inc_clock_inc_clock_typed" data_to_word_gcProofTheory.inc_clock_inc_clock;
val _ = pr_typed "mk_loc_jmup_exc_inc_clock_typed" data_to_word_gcProofTheory.mk_loc_jmup_exc_inc_clock;
val _ = pr_typed "jump_exc_inc_clock_EQ_NONE_typed" data_to_word_gcProofTheory.jump_exc_inc_clock_EQ_NONE;
val _ = pr_typed "state_rel_lookup_globals_typed" data_to_word_gcProofTheory.state_rel_lookup_globals;
val _ = pr_typed "state_rel_get_var_Block_typed" data_to_word_gcProofTheory.state_rel_get_var_Block;
val _ = pr_typed "jump_exc_push_env_NONE_simp_typed" data_to_word_gcProofTheory.jump_exc_push_env_NONE_simp;
val _ = pr_typed "s_key_eq_handler_eq_IMP_typed" data_to_word_gcProofTheory.s_key_eq_handler_eq_IMP;
val _ = pr_typed "eval_NONE_IMP_jump_exc_NONE_EQ_typed" data_to_word_gcProofTheory.eval_NONE_IMP_jump_exc_NONE_EQ;
val _ = pr_typed "jump_exc_push_env_SOME_typed" data_to_word_gcProofTheory.jump_exc_push_env_SOME;
val _ = pr_typed "eval_push_env_T_Raise_IMP_stack_length_typed" data_to_word_gcProofTheory.eval_push_env_T_Raise_IMP_stack_length;
val _ = pr_typed "eval_push_env_SOME_exc_IMP_s_key_eq_typed" data_to_word_gcProofTheory.eval_push_env_SOME_exc_IMP_s_key_eq;
val _ = pr_typed "eval_exc_stack_shorter_typed" data_to_word_gcProofTheory.eval_exc_stack_shorter;
val _ = pr_typed "NOT_1_domain_typed" data_to_word_gcProofTheory.NOT_1_domain;
val _ = pr_typed "NOT_3_domain_typed" data_to_word_gcProofTheory.NOT_3_domain;
val _ = pr_typed "NOT_5_domain_typed" data_to_word_gcProofTheory.NOT_5_domain;
val _ = pr_typed "cut_names_adjust_set_insert_1_typed" data_to_word_gcProofTheory.cut_names_adjust_set_insert_1;
val _ = pr_typed "cut_names_adjust_set_insert_3_typed" data_to_word_gcProofTheory.cut_names_adjust_set_insert_3;
val _ = pr_typed "case_EQ_SOME_IFF_typed" data_to_word_gcProofTheory.case_EQ_SOME_IFF;
val _ = pr_typed "state_rel_set_store_AllocSize_typed" data_to_word_gcProofTheory.state_rel_set_store_AllocSize;
val _ = pr_typed "inter_insert_typed" data_to_word_gcProofTheory.inter_insert;
val _ = pr_typed "lookup_0_adjust_set_typed" data_to_word_gcProofTheory.lookup_0_adjust_set;
val _ = pr_typed "lookup_1_adjust_set_typed" data_to_word_gcProofTheory.lookup_1_adjust_set;
val _ = pr_typed "lookup_3_adjust_set_typed" data_to_word_gcProofTheory.lookup_3_adjust_set;
val _ = pr_typed "lookup_5_adjust_set_typed" data_to_word_gcProofTheory.lookup_5_adjust_set;
val _ = pr_typed "lookup_ODD_adjust_set_typed" data_to_word_gcProofTheory.lookup_ODD_adjust_set;
val _ = pr_typed "wf_adjust_set_typed" data_to_word_gcProofTheory.wf_adjust_set;
val _ = pr_typed "lookup_adjust_set_typed" data_to_word_gcProofTheory.lookup_adjust_set;
val _ = pr_typed "adjust_set_inter_typed" data_to_word_gcProofTheory.adjust_set_inter;
val _ = pr_typed "state_rel_insert_1_typed" data_to_word_gcProofTheory.state_rel_insert_1;
val _ = pr_typed "state_rel_insert_3_typed" data_to_word_gcProofTheory.state_rel_insert_3;
val _ = pr_typed "state_rel_insert_7_typed" data_to_word_gcProofTheory.state_rel_insert_7;
val _ = pr_typed "state_rel_insert_3_1_typed" data_to_word_gcProofTheory.state_rel_insert_3_1;
val _ = pr_typed "state_rel_inc_clock_typed" data_to_word_gcProofTheory.state_rel_inc_clock;
val _ = pr_typed "word_gc_move_IMP_isWord_typed" data_to_word_gcProofTheory.word_gc_move_IMP_isWord;
val _ = pr_typed "word_gen_gc_move_IMP_isWord_typed" data_to_word_gcProofTheory.word_gen_gc_move_IMP_isWord;
val _ = pr_typed "word_gen_gc_partial_move_IMP_isWord_typed" data_to_word_gcProofTheory.word_gen_gc_partial_move_IMP_isWord;

(* Replay the local HOL theorem, which is not exported by the theory. *)
open word_gcFunctionsTheory wordSemTheory;
val word_gc_move_roots_IMP_FILTER0_replay = Q.prove(
  `∀ws i pa old m dm ws2 i2 pa2 m2 c2 c.
    word_gc_move_roots c (ws,i,pa,old,m,dm) = (ws2,i2,pa2,m2,c2) ∧
    EVERY loc_ok ws ⇒
    word_gc_move_roots c (FILTER isWord ws,i,pa,old,m,dm) =
                         (FILTER isWord ws2,i2,pa2,m2,c2)`,
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def]
  \\ Cases \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_gc_move_roots_def]
  THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ imp_res_tac word_gc_move_IMP_isWord
    \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
    \\ res_tac \\ fs [])
  \\ fs [isWord_def,word_gc_move_def,LET_DEF]
  \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
  \\ res_tac \\ fs [isWord_def]);
val _ = pr_typed "word_gc_move_roots_IMP_FILTER0_replay_typed" word_gc_move_roots_IMP_FILTER0_replay;

(* Replay the local generational theorem. *)
val word_gen_gc_move_roots_IMP_FILTER0_replay = Q.prove(
  `∀ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 c.
    word_gen_gc_move_roots c (ws,i,pa,ib,pb,old,m,dm) =
                             (ws2,i2,pa2,ib2,pb2,m2,c2) ∧
    EVERY loc_ok ws ⇒
    word_gen_gc_move_roots c (FILTER isWord ws,i,pa,ib,pb,old,m,dm) =
                             (FILTER isWord ws2,i2,pa2,ib2,pb2,m2,c2)`,
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def]
  \\ Cases \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_gen_gc_move_roots_def]
  THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ imp_res_tac word_gen_gc_move_IMP_isWord
    \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
    \\ res_tac \\ fs [])
  \\ fs [isWord_def,word_gen_gc_move_def,LET_DEF]
  \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
  \\ res_tac \\ fs [isWord_def]);
val _ = pr_typed "word_gen_gc_move_roots_IMP_FILTER0_replay_typed" word_gen_gc_move_roots_IMP_FILTER0_replay;

(* Replay the first of two declarations with this HOL name. *)
val word_gen_gc_partial_move_roots_IMP_FILTER_first_replay = Q.prove(
  `∀ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 c.
    word_gen_gc_partial_move_roots c (ws,i,pa,old,m,dm,gs,rs) =
                                     (ws2,i2,pa2,m2,c2) ∧
    EVERY loc_ok ws ⇒
    word_gen_gc_partial_move_roots c (FILTER isWord ws,i,pa,old,m,dm,gs,rs) =
                                     (FILTER isWord ws2,i2,pa2,m2,c2)`,
  Induct \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def]
  \\ Cases \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_gen_gc_partial_move_roots_def]
  THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ imp_res_tac word_gen_gc_partial_move_IMP_isWord
    \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
    \\ res_tac \\ fs [])
  \\ fs [isWord_def,word_gen_gc_partial_move_def,LET_DEF]
  \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
  \\ res_tac \\ fs [isWord_def]);
val _ = pr_typed "word_gen_gc_partial_move_roots_IMP_FILTER_first_replay_typed" word_gen_gc_partial_move_roots_IMP_FILTER_first_replay;
val _ = pr_typed "word_gc_fun_APPEND_IMP_typed" data_to_word_gcProofTheory.word_gc_fun_APPEND_IMP;
val _ = pr_typed "IMP_loc_merge_APPEND_typed" data_to_word_gcProofTheory.IMP_loc_merge_APPEND;
val _ = pr_typed "TAKE_DROP_loc_merge_APPEND_typed" data_to_word_gcProofTheory.TAKE_DROP_loc_merge_APPEND;
val _ = pr_typed "loc_merge_NIL_typed" data_to_word_gcProofTheory.loc_merge_NIL;
val _ = pr_typed "loc_merge_APPEND_typed" data_to_word_gcProofTheory.loc_merge_APPEND;
val _ = pr_typed "EVERY2_loc_merge_typed" data_to_word_gcProofTheory.EVERY2_loc_merge;
val _ = pr_typed "ALOOKUP_ZIP_typed" data_to_word_gcProofTheory.ALOOKUP_ZIP;
val _ = pr_typed "join_env_NIL_typed" data_to_word_gcProofTheory.join_env_NIL;
val _ = pr_typed "join_env_CONS_typed" data_to_word_gcProofTheory.join_env_CONS;
val _ = pr_typed "stack_rel_simp_typed" data_to_word_gcProofTheory.stack_rel_simp;
val _ = pr_typed "join_env_EQ_ZIP_typed" data_to_word_gcProofTheory.join_env_EQ_ZIP;
val _ = pr_typed "LENGTH_MAP_SND_join_env_IMP_typed" data_to_word_gcProofTheory.LENGTH_MAP_SND_join_env_IMP;
val _ = pr_typed "lemma1_typed" data_to_word_gcProofTheory.lemma1;
val _ = pr_typed "word_ml_inv_cons_snoc_typed" data_to_word_gcProofTheory.word_ml_inv_cons_snoc;
val _ = pr_typed "toListA_mk_typed" data_to_word_gcProofTheory.toListA_mk;
val _ = pr_typed "PERM_lookup_toList_lemma_typed" data_to_word_gcProofTheory.PERM_lookup_toList_lemma;
val _ = pr_typed "get_vars_sing_typed" data_to_word_gcProofTheory.get_vars_sing;
val _ = pr_typed "adjust_var_not_15_typed" data_to_word_gcProofTheory.adjust_var_not_15;
val _ = pr_typed "memory_rel_Temp_typed" data_to_word_gcProofTheory.memory_rel_Temp;
val _ = pr_typed "MustTerminate_limit_NOT_0_typed" data_to_word_gcProofTheory.MustTerminate_limit_NOT_0;
val _ = pr_typed "join_env_locals_def_typed" data_to_word_gcProofTheory.join_env_locals_def;
val _ = pr_typed "join_env_locals_insert_odd_typed" data_to_word_gcProofTheory.join_env_locals_insert_odd;
val _ = pr_typed "join_env_locals_insert_dest_odd_typed" data_to_word_gcProofTheory.join_env_locals_insert_dest_odd;
val _ = pr_typed "inter_insert_ODD_adjust_set_alt_typed" data_to_word_gcProofTheory.inter_insert_ODD_adjust_set_alt;
val _ = pr_typed "get_vars_termdep_typed" data_to_word_gcProofTheory.get_vars_termdep;
val _ = pr_typed "inter_delete_ODD_adjust_set_alt_typed" data_to_word_gcProofTheory.inter_delete_ODD_adjust_set_alt;
val _ = pr_typed "inter_insert_ODD_adjust_set_typed" data_to_word_gcProofTheory.inter_insert_ODD_adjust_set;
