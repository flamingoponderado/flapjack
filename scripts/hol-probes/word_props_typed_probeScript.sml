(* Typed source declarations for wordProps (task 148). *)
load "preamble";
load "wordPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble wordPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="wordProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by wordProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of wordProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "env_to_list_lookup_equiv_typed" "env_to_list_lookup_equiv";
val _ = emit "alloc_const_typed" "alloc_const";
val _ = emit "evaluate_add_clock_typed" "evaluate_add_clock";
val _ = emit "evaluate_add_clock_io_events_mono_typed" "evaluate_add_clock_io_events_mono";
val _ = emit "alloc_code_gc_fun_const_typed" "alloc_code_gc_fun_const";
val _ = emit "evaluate_consts_typed" "evaluate_consts";
val _ = emit "pop_env_code_gc_fun_clock_typed" "pop_env_code_gc_fun_clock";
val _ = emit "evaluate_dec_clock_typed" "evaluate_dec_clock";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "cut_state_const_typed" "cut_state_const";
val _ = emit "evaluate_stack_limit_typed" "evaluate_stack_limit";
val _ = emit "evaluate_stack_limit_stack_max_typed" "evaluate_stack_limit_stack_max";
val _ = emit "evaluate_stack_limit_stack_max_eq_typed" "evaluate_stack_limit_stack_max_eq";
val _ = emit "evaluate_stack_max_typed" "evaluate_stack_max";
val _ = emit "evaluate_stack_max_IS_SOME_typed" "evaluate_stack_max_IS_SOME";
val _ = emit "evaluate_stack_max_le_typed" "evaluate_stack_max_le";
val _ = emit "share_inst_const_typed" "share_inst_const";
val _ = emit "evaluate_stack_swap_typed" "evaluate_stack_swap";
val _ = emit "gc_const_typed" "gc_const";
val _ = emit "gc_fun_ok_def_typed" "gc_fun_ok_def";
val _ = emit "inst_const_typed" "inst_const";
val _ = emit "inst_const_full_typed" "inst_const_full";
val _ = emit "jump_exc_const_typed" "jump_exc_const";
val _ = emit "locals_rel_alist_insert_typed" "locals_rel_alist_insert";
val _ = emit "locals_rel_cut_env_typed" "locals_rel_cut_env";
val _ = emit "locals_rel_cut_envs_typed" "locals_rel_cut_envs";
val _ = emit "locals_rel_evaluate_thm_typed" "locals_rel_evaluate_thm";
val _ = emit "locals_rel_get_var_typed" "locals_rel_get_var";
val _ = emit "locals_rel_get_var_imm_typed" "locals_rel_get_var_imm";
val _ = emit "locals_rel_get_var_imm_simp_typed" "locals_rel_get_var_imm_simp";
val _ = emit "locals_rel_get_var_simp_typed" "locals_rel_get_var_simp";
val _ = emit "locals_rel_get_vars_typed" "locals_rel_get_vars";
val _ = emit "locals_rel_get_vars_simp_typed" "locals_rel_get_vars_simp";
val _ = emit "locals_rel_word_exp_typed" "locals_rel_word_exp";
val _ = emit "locals_rel_word_exp_simp_typed" "locals_rel_word_exp_simp";
val _ = emit "the_words_EVERY_IS_SOME_typed" "the_words_EVERY_IS_SOME";
val _ = emit "locals_rel_def_typed" "locals_rel_def";
val _ = emit "mem_store_const_typed" "mem_store_const";
val _ = emit "no_install_code_def_typed" "no_install_code_def";
val _ = emit "no_alloc_code_def_typed" "no_alloc_code_def";
val _ = emit "no_alloc_find_code_typed" "no_alloc_find_code";
val _ = emit "no_install_evaluate_const_code_typed" "no_install_evaluate_const_code";
val _ = emit "no_install_find_code_typed" "no_install_find_code";
val _ = emit "no_mt_code_def_typed" "no_mt_code_def";
val _ = emit "permute_swap_lemma_typed" "permute_swap_lemma";
val _ = emit "ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME_typed" "ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME";
val _ = emit "env_to_list_ALL_DISTINCT_typed" "env_to_list_ALL_DISTINCT";
val _ = emit "env_to_list_ALL_DISTINCT_FST_typed" "env_to_list_ALL_DISTINCT_FST";
val _ = emit "env_to_list_PERM_typed" "env_to_list_PERM";
val _ = emit "PERM_fromAList_typed" "PERM_fromAList";
val _ = emit "PERM_list_rearrange_typed" "PERM_list_rearrange";
val _ = emit "permute_swap_lemma2_typed" "permute_swap_lemma2";
val _ = emit "permute_swap_lemma3_typed" "permute_swap_lemma3";
val _ = emit "stack_size_perm_typed" "stack_size_perm";
val _ = emit "pop_env_const_typed" "pop_env_const";
val _ = emit "s_frame_key_eq_def_typed" "s_frame_key_eq_def";
val _ = emit "s_frame_key_eq_def2_typed" "s_frame_key_eq_def2";
val _ = emit "s_frame_key_eq_refl_typed" "s_frame_key_eq_refl";
val _ = emit "s_frame_val_eq_def_typed" "s_frame_val_eq_def";
val _ = emit "s_frame_val_eq_def2_typed" "s_frame_val_eq_def2";
val _ = emit "s_frame_val_eq_refl_typed" "s_frame_val_eq_refl";
val _ = emit "s_key_eq_def_typed" "s_key_eq_def";
val _ = emit "s_key_eq_refl_typed" "s_key_eq_refl";
val _ = emit "s_val_and_key_eq_typed" "s_val_and_key_eq";
val _ = emit "s_val_eq_def_typed" "s_val_eq_def";
val _ = emit "s_val_eq_refl_typed" "s_val_eq_refl";
val _ = emit "LASTN_LENGTH_cond_typed" "LASTN_LENGTH_cond";
val _ = emit "s_key_eq_stack_size_typed" "s_key_eq_stack_size";
val _ = emit "s_key_eq_tail_typed" "s_key_eq_tail";
val _ = emit "s_val_append_eq_stack_size_typed" "s_val_append_eq_stack_size";
val _ = emit "s_val_eq_LASTN_exists_typed" "s_val_eq_LASTN_exists";
val _ = emit "s_val_eq_stack_size_typed" "s_val_eq_stack_size";
val _ = emit "gc_s_key_eq_typed" "gc_s_key_eq";
val _ = emit "gc_s_val_eq_typed" "gc_s_val_eq";
val _ = emit "gc_s_val_eq_gen_typed" "gc_s_val_eq_gen";
val _ = emit "gc_s_val_eq_word_state_typed" "gc_s_val_eq_word_state";
val _ = emit "push_env_pop_env_s_key_eq_typed" "push_env_pop_env_s_key_eq";
val _ = emit "s_key_eq_length_typed" "s_key_eq_length";
val _ = emit "s_key_eq_sym_typed" "s_key_eq_sym";
val _ = emit "s_key_eq_trans_typed" "s_key_eq_trans";
val _ = emit "s_val_eq_length_typed" "s_val_eq_length";
val _ = emit "s_val_eq_sym_typed" "s_val_eq_sym";
val _ = emit "s_val_eq_trans_typed" "s_val_eq_trans";
val _ = emit "alloc_with_const_typed" "alloc_with_const";
val _ = emit "assign_const_typed" "assign_const";
val _ = emit "assign_const_full_typed" "assign_const_full";
val _ = emit "assign_with_const_typed" "assign_with_const";
val _ = emit "call_env_const_typed" "call_env_const";
val _ = emit "call_env_with_const_typed" "call_env_with_const";
val _ = emit "cut_state_with_const_typed" "cut_state_with_const";
val _ = emit "dec_clock_const_typed" "dec_clock_const";
val _ = emit "flush_state_const_typed" "flush_state_const";
val _ = emit "flush_state_with_const_typed" "flush_state_with_const";
val _ = emit "gc_with_const_typed" "gc_with_const";
val _ = emit "get_fp_var_set_fp_var_typed" "get_fp_var_set_fp_var";
val _ = emit "get_fp_var_with_const_typed" "get_fp_var_with_const";
val _ = emit "get_store_set_store_typed" "get_store_set_store";
val _ = emit "get_store_with_const_typed" "get_store_with_const";
val _ = emit "get_var_imm_with_const_typed" "get_var_imm_with_const";
val _ = emit "get_var_set_fp_var_typed" "get_var_set_fp_var";
val _ = emit "get_var_set_store_typed" "get_var_set_store";
val _ = emit "get_var_with_const_typed" "get_var_with_const";
val _ = emit "get_vars_with_const_typed" "get_vars_with_const";
val _ = emit "has_space_with_const_typed" "has_space_with_const";
val _ = emit "inst_with_const_typed" "inst_with_const";
val _ = emit "jump_exc_with_const_typed" "jump_exc_with_const";
val _ = emit "mem_load_with_const_typed" "mem_load_with_const";
val _ = emit "mem_store_with_const_typed" "mem_store_with_const";
val _ = emit "OPTION_CASE_OPTION_MAP_typed" "OPTION_CASE_OPTION_MAP";
val _ = emit "OPTION_CASE_MAP_typed" "OPTION_CASE_MAP";
val _ = emit "pop_env_with_const_typed" "pop_env_with_const";
val _ = emit "PAIR_MAP_EQ_PAIR_typed" "PAIR_MAP_EQ_PAIR";
val _ = emit "push_env_const_typed" "push_env_const";
val _ = emit "push_env_with_const_typed" "push_env_with_const";
val _ = emit "set_fp_var_const_typed" "set_fp_var_const";
val _ = emit "set_fp_var_with_const_typed" "set_fp_var_with_const";
val _ = emit "set_store_with_const_typed" "set_store_with_const";
val _ = emit "set_vars_const_typed" "set_vars_const";
val _ = emit "set_vars_with_const_typed" "set_vars_with_const";
val _ = emit "sh_mem_load16_with_const_typed" "sh_mem_load16_with_const";
val _ = emit "sh_mem_load32_with_const_typed" "sh_mem_load32_with_const";
val _ = emit "sh_mem_load_byte_with_const_typed" "sh_mem_load_byte_with_const";
val _ = emit "sh_mem_load_with_const_typed" "sh_mem_load_with_const";
val _ = emit "sh_mem_set_var_const_typed" "sh_mem_set_var_const";
val _ = emit "sh_mem_set_var_with_const_typed" "sh_mem_set_var_with_const";
val _ = emit "sh_mem_store16_const_typed" "sh_mem_store16_const";
val _ = emit "sh_mem_store16_with_const_typed" "sh_mem_store16_with_const";
val _ = emit "sh_mem_store32_const_typed" "sh_mem_store32_const";
val _ = emit "sh_mem_store32_with_const_typed" "sh_mem_store32_with_const";
val _ = emit "sh_mem_store_byte_const_typed" "sh_mem_store_byte_const";
val _ = emit "sh_mem_store_byte_with_const_typed" "sh_mem_store_byte_with_const";
val _ = emit "sh_mem_store_const_typed" "sh_mem_store_const";
val _ = emit "sh_mem_store_with_const_typed" "sh_mem_store_with_const";
val _ = emit "share_inst_with_const_typed" "share_inst_with_const";
val _ = emit "state_const_typed" "state_const";
val _ = emit "unset_var_const_typed" "unset_var_const";
val _ = emit "unset_var_with_const_typed" "unset_var_with_const";
val _ = emit "word_exp_with_const_typed" "word_exp_with_const";
val _ = emit "get_var_set_var_typed" "get_var_set_var";
val _ = emit "get_vars_length_lemma_typed" "get_vars_length_lemma";
val _ = emit "LASTN_stack_size_SOME_typed" "LASTN_stack_size_SOME";
val _ = emit "mem_list_rearrange_typed" "mem_list_rearrange";
val _ = emit "s_key_eq_def2_typed" "s_key_eq_def2";
val _ = emit "set_store_const_typed" "set_store_const";
val _ = emit "set_var_const_typed" "set_var_const";
val _ = emit "set_var_with_const_typed" "set_var_with_const";
val _ = emit "stack_size_eq_typed" "stack_size_eq";
val _ = emit "stack_size_eq2_typed" "stack_size_eq2";
val _ = emit "evaluate_code_only_grows_typed" "evaluate_code_only_grows";
val _ = emit "evaluate_NONE_stack_size_const_typed" "evaluate_NONE_stack_size_const";
