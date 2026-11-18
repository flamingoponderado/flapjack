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
