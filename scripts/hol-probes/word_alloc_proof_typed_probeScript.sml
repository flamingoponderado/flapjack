(* Typed source declarations for word_allocProof (task 148). *)
load "preamble";
load "word_allocProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_allocProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_allocProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_allocProof")
  | SOME (th,_) => show label th;

val _ = emit "pre_post_conventions_word_alloc_typed" "pre_post_conventions_word_alloc";
val _ = emit "check_col_INJ_typed" "check_col_INJ";
val _ = emit "check_partial_col_INJ_typed" "check_partial_col_INJ";
val _ = emit "clash_tree_colouring_ok_typed" "clash_tree_colouring_ok";
val _ = emit "every_stack_var_apply_colour_typed" "every_stack_var_apply_colour";
val _ = emit "every_var_exp_apply_colour_exp_typed" "every_var_exp_apply_colour_exp";
val _ = emit "every_var_inst_apply_colour_inst_typed" "every_var_inst_apply_colour_inst";
val _ = emit "every_var_apply_colour_typed" "every_var_apply_colour";
val _ = emit "colouring_ok_def_typed" "colouring_ok_def";
val _ = emit "cut_env_lemma_typed" "cut_env_lemma";
val _ = emit "cut_envs_lemma_typed" "cut_envs_lemma";
val _ = emit "cut_names_lemma_typed" "cut_names_lemma";
val _ = emit "gc_frame_typed" "gc_frame";
val _ = emit "INJ_union_typed" "INJ_union";
val _ = emit "key_map_implies_typed" "key_map_implies";
val _ = emit "list_rearrange_keys_typed" "list_rearrange_keys";
val _ = emit "list_rearrange_keys_2_typed" "list_rearrange_keys_2";
val _ = emit "list_rearrange_MAP_typed" "list_rearrange_MAP";
val _ = emit "MAP_FST_list_rearrange_keys_SORT_typed" "MAP_FST_list_rearrange_keys_SORT";
val _ = emit "evaluate_apply_colour_typed" "evaluate_apply_colour";
val _ = emit "evaluate_remove_dead_typed" "evaluate_remove_dead";
val _ = emit "evaluate_remove_dead_prog_typed" "evaluate_remove_dead_prog";
val _ = emit "even_starting_locals_def_typed" "even_starting_locals_def";
val _ = emit "full_ssa_cc_trans_correct_typed" "full_ssa_cc_trans_correct";
val _ = emit "word_alloc_full_inst_ok_less_typed" "word_alloc_full_inst_ok_less";
val _ = emit "ALOOKUP_key_remap_INJ_typed" "ALOOKUP_key_remap_INJ";
val _ = emit "ALOOKUP_key_remap_2_typed" "ALOOKUP_key_remap_2";
val _ = emit "max_var_max_typed" "max_var_max";
val _ = emit "IMAGE_DIFF_typed" "IMAGE_DIFF";
val _ = emit "domain_numset_list_insert_typed" "domain_numset_list_insert";
val _ = emit "permute_swap_lemma4_typed" "permute_swap_lemma4";
val _ = emit "pop_env_frame_typed" "pop_env_frame";
val _ = emit "push_env_s_val_eq_typed" "push_env_s_val_eq";
val _ = emit "s_key_eq_push_env_imp_MAP_FST_typed" "s_key_eq_push_env_imp_MAP_FST";
val _ = emit "s_key_eq_val_eq_pop_env_typed" "s_key_eq_val_eq_pop_env";
val _ = emit "live_store_rel_def_typed" "live_store_rel_def";
val _ = emit "live_store_rel_FLOOKUP_store_typed" "live_store_rel_FLOOKUP_store";
val _ = emit "live_store_rel_less_typed" "live_store_rel_less";
val _ = emit "nlive_store_def_typed" "nlive_store_def";
val _ = emit "every_name_def2_typed" "every_name_def2";
val _ = emit "ssa_cc_trans_pre_alloc_conventions_typed" "ssa_cc_trans_pre_alloc_conventions";
val _ = emit "ssa_cc_trans_full_inst_ok_less_typed" "ssa_cc_trans_full_inst_ok_less";
val _ = emit "full_ssa_cc_trans_distinct_tar_reg_typed" "full_ssa_cc_trans_distinct_tar_reg";
val _ = emit "ssa_cc_trans_distinct_tar_reg_typed" "ssa_cc_trans_distinct_tar_reg";
val _ = emit "full_ssa_cc_trans_pre_alloc_conventions_typed" "full_ssa_cc_trans_pre_alloc_conventions";
val _ = emit "full_ssa_cc_trans_full_inst_ok_less_typed" "full_ssa_cc_trans_full_inst_ok_less";
val _ = emit "cut_envs_domain_SUBSET_typed" "cut_envs_domain_SUBSET";
val _ = emit "ssa_locals_rel_def_typed" "ssa_locals_rel_def";
val _ = emit "ssa_locals_rel_delete_left_typed" "ssa_locals_rel_delete_left";
val _ = emit "ssa_locals_rel_delete_right_typed" "ssa_locals_rel_delete_right";
val _ = emit "ssa_locals_rel_force_rename_typed" "ssa_locals_rel_force_rename";
val _ = emit "lt_ok_def_typed" "lt_ok_def";
val _ = emit "ssa_map_ok_def_typed" "ssa_map_ok_def";
val _ = emit "ssa_map_ok_insert_typed" "ssa_map_ok_insert";
val _ = emit "domain_force_rename_typed" "domain_force_rename";
val _ = emit "lookup_force_rename_typed" "lookup_force_rename";
val _ = emit "lookup_force_rename_aux_typed" "lookup_force_rename_aux";
val _ = emit "ssa_map_ok_force_rename_typed" "ssa_map_ok_force_rename";
val _ = emit "ssa_cc_trans_props_typed" "ssa_cc_trans_props";
val _ = emit "list_next_var_rename_move_distinct_typed" "list_next_var_rename_move_distinct";
val _ = emit "ssa_cc_trans_correct_typed" "ssa_cc_trans_correct";
val _ = emit "select_reg_alloc_correct_typed" "select_reg_alloc_correct";
val _ = emit "word_state_eq_rel_def_typed" "word_state_eq_rel_def";
val _ = emit "strong_locals_rel_def_typed" "strong_locals_rel_def";
val _ = emit "strong_locals_rel_insert_typed" "strong_locals_rel_insert";
val _ = emit "strong_locals_rel_UNION_typed" "strong_locals_rel_UNION";
val _ = emit "strong_locals_rel_set_var_dom_typed" "strong_locals_rel_set_var_dom";
val _ = emit "strong_locals_rel_set_vars_dom_typed" "strong_locals_rel_set_vars_dom";
val _ = emit "word_alloc_correct_typed" "word_alloc_correct";
