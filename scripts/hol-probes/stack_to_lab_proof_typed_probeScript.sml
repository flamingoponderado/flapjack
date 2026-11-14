(* Typed source declarations for stack_to_labProof (task 148). *)
load "preamble";
load "stack_to_labProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble stack_to_labProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stack_to_labProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stack_to_labProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stack_to_labProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "ALOOKUP_PARTITION_typed" "ALOOKUP_PARTITION";
val _ = emit "asm_fetch_aux_add_typed" "asm_fetch_aux_add";
val _ = emit "asm_fetch_aux_SOME_append2_typed" "asm_fetch_aux_SOME_append2";
val _ = emit "code_installed_def_typed" "code_installed_def";
val _ = emit "code_installed_APPEND_typed" "code_installed_APPEND";
val _ = emit "code_installed_append2_typed" "code_installed_append2";
val _ = emit "code_installed_append_imp_typed" "code_installed_append_imp";
val _ = emit "code_installed_cons_typed" "code_installed_cons";
val _ = emit "code_installed_eq_typed" "code_installed_eq";
val _ = emit "code_installed_isPREFIX_typed" "code_installed_isPREFIX";
val _ = emit "code_installed_prog_to_section_typed" "code_installed_prog_to_section";
val _ = emit "labels_ok_def_typed" "labels_ok_def";
val _ = emit "labels_ok_imp_typed" "labels_ok_imp";
val _ = emit "labels_ok_labs_correct_typed" "labels_ok_labs_correct";
val _ = emit "labs_correct_def_typed" "labs_correct_def";
val _ = emit "labs_correct_append_typed" "labs_correct_append";
val _ = emit "labs_correct_hd_typed" "labs_correct_hd";
val _ = emit "loc_to_pc_APPEND_typed" "loc_to_pc_APPEND";
val _ = emit "loc_to_pc_append2_typed" "loc_to_pc_append2";
val _ = emit "loc_to_pc_isPREFIX_typed" "loc_to_pc_isPREFIX";
val _ = emit "loc_to_pc_skip_section_typed" "loc_to_pc_skip_section";
val _ = emit "MAP_prog_to_section_Section_num_typed" "MAP_prog_to_section_Section_num";
val _ = emit "next_lab_non_zero_typed" "next_lab_non_zero";
val _ = emit "stack_to_lab_compile_lab_pres_typed" "stack_to_lab_compile_lab_pres";
val _ = emit "compile_all_enc_ok_pre_typed" "compile_all_enc_ok_pre";
val _ = emit "EVERY_sec_ends_with_label_MAP_prog_to_section_typed" "EVERY_sec_ends_with_label_MAP_prog_to_section";
val _ = emit "full_make_init_has_fp_ops_typed" "full_make_init_has_fp_ops";
val _ = emit "IMP_init_state_ok_typed" "IMP_init_state_ok";
val _ = emit "IMP_init_store_ok_typed" "IMP_init_store_ok";
val _ = emit "stack_to_lab_compile_all_enc_ok_typed" "stack_to_lab_compile_all_enc_ok";
val _ = emit "flatten_call_correct_typed" "flatten_call_correct";
val _ = emit "halt_assum_def_typed" "halt_assum_def";
val _ = emit "flatten_correct_typed" "flatten_correct";
val _ = dt_label "result_view_typed" "result_view";
val _ = emit "compile_jump_correct_typed" "compile_jump_correct";
val _ = emit "every_is_some_loc_to_pc_prefix_typed" "every_is_some_loc_to_pc_prefix";
val _ = emit "flatten_leq_typed" "flatten_leq";
val _ = emit "flatten_T_F_typed" "flatten_T_F";
val _ = emit "halt_view_def_typed" "halt_view_def";
val _ = emit "halt_word_view_def_typed" "halt_word_view_def";
val _ = emit "is_some_loc_to_pc_prefix_typed" "is_some_loc_to_pc_prefix";
val _ = emit "no_ret_correct_typed" "no_ret_correct";
val _ = emit "NOT_MEM_find_lab_IMP_typed" "NOT_MEM_find_lab_IMP";
val _ = emit "prog_to_section_labels_ok_typed" "prog_to_section_labels_ok";
val _ = emit "result_view_def_typed" "result_view_def";
val _ = emit "stack_to_lab_lab_pres_typed" "stack_to_lab_lab_pres";
val _ = emit "stack_to_lab_lab_pres_T_typed" "stack_to_lab_lab_pres_T";
val _ = emit "flatten_semantics_typed" "flatten_semantics";
val _ = emit "full_make_init_def_typed" "full_make_init_def";
val _ = emit "full_make_init_buffer_typed" "full_make_init_buffer";
val _ = emit "full_make_init_compile_typed" "full_make_init_compile";
val _ = emit "full_make_init_ffi_typed" "full_make_init_ffi";
val _ = emit "full_make_init_semantics_typed" "full_make_init_semantics";
val _ = emit "contain_def_typed" "contain_def";
val _ = emit "good_code_def_typed" "good_code_def";
val _ = emit "IN_domain_collect_info_typed" "IN_domain_collect_info";
val _ = emit "IN_get_code_labels_comp_top_typed" "IN_get_code_labels_comp_top";
val _ = emit "IN_get_code_labels_comp_top_lemma_typed" "IN_get_code_labels_comp_top_lemma";
val _ = emit "stack_alloc_stack_good_code_labels_typed" "stack_alloc_stack_good_code_labels";
val _ = emit "stack_alloc_stack_good_code_labels_incr_typed" "stack_alloc_stack_good_code_labels_incr";
val _ = emit "stack_names_get_code_labels_typed" "stack_names_get_code_labels";
val _ = emit "stack_names_stack_good_code_labels_typed" "stack_names_stack_good_code_labels";
val _ = emit "stack_rawcall_stack_good_code_labels_typed" "stack_rawcall_stack_good_code_labels";
val _ = emit "stack_remove_stack_good_code_labels_typed" "stack_remove_stack_good_code_labels";
val _ = emit "stack_remove_stack_good_code_labels_incr_typed" "stack_remove_stack_good_code_labels_incr";
val _ = emit "stack_to_lab_stack_good_code_labels_typed" "stack_to_lab_stack_good_code_labels";
val _ = emit "stack_to_lab_stack_good_code_labels_incr_typed" "stack_to_lab_stack_good_code_labels_incr";
val _ = emit "nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels_typed" "nonzero_get_labels_MAP_prog_to_section_SUBSET_code_labels";
val _ = emit "restrict_nonzero_IN_typed" "restrict_nonzero_IN";
val _ = emit "restrict_nonzero_union_typed" "restrict_nonzero_union";
val _ = emit "stack_alloc_stack_good_handler_labels_typed" "stack_alloc_stack_good_handler_labels";
val _ = emit "stack_alloc_stack_good_handler_labels_incr_typed" "stack_alloc_stack_good_handler_labels_incr";
val _ = emit "stack_good_handler_labels_append_typed" "stack_good_handler_labels_append";
val _ = emit "stack_names_stack_good_handler_labels_typed" "stack_names_stack_good_handler_labels";
val _ = emit "stack_rawcall_stack_good_handler_labels_typed" "stack_rawcall_stack_good_handler_labels";
val _ = emit "stack_remove_stack_good_handler_labels_typed" "stack_remove_stack_good_handler_labels";
val _ = emit "stack_remove_stack_good_handler_labels_incr_typed" "stack_remove_stack_good_handler_labels_incr";
val _ = emit "stack_to_lab_stack_good_handler_labels_typed" "stack_to_lab_stack_good_handler_labels";
val _ = emit "stack_to_lab_stack_good_handler_labels_incr_typed" "stack_to_lab_stack_good_handler_labels_incr";
val _ = emit "inst_correct_typed" "inst_correct";
val _ = emit "complex_get_code_labels_def_typed" "complex_get_code_labels_def";
val _ = emit "flatten_preserves_handler_labels_typed" "flatten_preserves_handler_labels";
val _ = emit "get_labels_MAP_prog_to_section_SUBSET_code_labels_typed" "get_labels_MAP_prog_to_section_SUBSET_code_labels";
val _ = emit "get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma_typed" "get_labels_MAP_prog_to_section_SUBSET_code_labels_lemma";
val _ = emit "MAP_prog_to_section_preserves_handler_labels_typed" "MAP_prog_to_section_preserves_handler_labels";
val _ = emit "one_prog_section_typed" "one_prog_section";
val _ = emit "prog_to_section_labels_typed" "prog_to_section_labels";
val _ = emit "make_init_def_typed" "make_init_def";
val _ = emit "memory_assumption_def_typed" "memory_assumption_def";
val _ = emit "state_rel_make_init_typed" "state_rel_make_init";
val _ = emit "asm_fetch_aux_no_install_CONS_typed" "asm_fetch_aux_no_install_CONS";
val _ = emit "stack_to_lab_compile_no_install_typed" "stack_to_lab_compile_no_install";
val _ = emit "downshift_no_install_typed" "downshift_no_install";
val _ = emit "flatten_no_install_typed" "flatten_no_install";
val _ = emit "prog_to_section_no_install_typed" "prog_to_section_no_install";
val _ = emit "stack_alloc_comp_no_install_typed" "stack_alloc_comp_no_install";
val _ = emit "stack_alloc_compile_no_install_typed" "stack_alloc_compile_no_install";
val _ = emit "stack_alloc_no_install_typed" "stack_alloc_no_install";
val _ = emit "stack_alloc_prog_comp_no_install_typed" "stack_alloc_prog_comp_no_install";
val _ = emit "stack_free_no_install_typed" "stack_free_no_install";
val _ = emit "stack_names_comp_no_install_typed" "stack_names_comp_no_install";
val _ = emit "stack_names_compile_no_install_typed" "stack_names_compile_no_install";
val _ = emit "stack_names_prog_comp_no_install_typed" "stack_names_prog_comp_no_install";
val _ = emit "stack_rawcall_comp_no_install_typed" "stack_rawcall_comp_no_install";
val _ = emit "stack_rawcall_comp_top_no_install_typed" "stack_rawcall_comp_top_no_install";
val _ = emit "stack_rawcall_compile_no_install_typed" "stack_rawcall_compile_no_install";
val _ = emit "stack_remove_comp_no_install_typed" "stack_remove_comp_no_install";
val _ = emit "stack_remove_compile_no_install_typed" "stack_remove_compile_no_install";
val _ = emit "stack_remove_prog_comp_no_install_typed" "stack_remove_prog_comp_no_install";
val _ = emit "upshift_no_install_typed" "upshift_no_install";
val _ = emit "asm_fetch_aux_no_share_mem_inst_CONS_typed" "asm_fetch_aux_no_share_mem_inst_CONS";
val _ = emit "compile_no_share_mem_inst_typed" "compile_no_share_mem_inst";
val _ = emit "compile_no_stubs_no_share_mem_inst_typed" "compile_no_stubs_no_share_mem_inst";
val _ = emit "downshift_no_shmemop_typed" "downshift_no_shmemop";
val _ = emit "flatten_no_share_mem_inst_typed" "flatten_no_share_mem_inst";
val _ = emit "prog_to_section_no_share_mem_inst_typed" "prog_to_section_no_share_mem_inst";
val _ = emit "stack_alloc_comp_no_shmemop_typed" "stack_alloc_comp_no_shmemop";
val _ = emit "stack_alloc_compile_no_shmemop_typed" "stack_alloc_compile_no_shmemop";
val _ = emit "stack_alloc_no_shmemop_typed" "stack_alloc_no_shmemop";
val _ = emit "stack_alloc_prog_comp_no_shmemop_typed" "stack_alloc_prog_comp_no_shmemop";
val _ = emit "stack_free_no_shmemop_typed" "stack_free_no_shmemop";
val _ = emit "stack_names_comp_no_shmemop_typed" "stack_names_comp_no_shmemop";
val _ = emit "stack_names_compile_no_shmemop_typed" "stack_names_compile_no_shmemop";
val _ = emit "stack_names_prog_comp_no_shmemop_typed" "stack_names_prog_comp_no_shmemop";
val _ = emit "stack_rawcall_comp_no_shmemop_typed" "stack_rawcall_comp_no_shmemop";
val _ = emit "stack_rawcall_comp_top_no_shmemop_typed" "stack_rawcall_comp_top_no_shmemop";
val _ = emit "stack_rawcall_compile_no_shmemop_typed" "stack_rawcall_compile_no_shmemop";
val _ = emit "stack_remove_comp_no_shmemop_typed" "stack_remove_comp_no_shmemop";
val _ = emit "stack_remove_compile_no_shmemop_typed" "stack_remove_compile_no_shmemop";
val _ = emit "stack_remove_prog_comp_no_shmemop_typed" "stack_remove_prog_comp_no_shmemop";
val _ = emit "stack_remove_prog_comp_no_shmemop_MAP_typed" "stack_remove_prog_comp_no_shmemop_MAP";
val _ = emit "upshift_no_shmemop_typed" "upshift_no_shmemop";
val _ = emit "asm_fetch_aux_no_label_typed" "asm_fetch_aux_no_label";
val _ = emit "assert_T_typed" "assert_T";
val _ = emit "dest_to_loc_def_typed" "dest_to_loc_def";
val _ = emit "find_code_lookup_typed" "find_code_lookup";
val _ = emit "not_is_Label_compile_jump_typed" "not_is_Label_compile_jump";
val _ = emit "word_cmp_negate_typed" "word_cmp_negate";
val _ = emit "word_cmp_negate_alt_typed" "word_cmp_negate_alt";
val _ = emit "word_cmp_not_NONE_typed" "word_cmp_not_NONE";
val _ = emit "word_sh_word_shift_typed" "word_sh_word_shift";
val _ = emit "loc_check_IMP_loc_to_pc_typed" "loc_check_IMP_loc_to_pc";
val _ = emit "mem_store_upd_mem_typed" "mem_store_upd_mem";
val _ = emit "set_fp_var_upd_fp_reg_typed" "set_fp_var_upd_fp_reg";
val _ = emit "set_var_upd_reg_typed" "set_var_upd_reg";
val _ = emit "set_var_Word_upd_reg_typed" "set_var_Word_upd_reg";
val _ = emit "state_rel_def_typed" "state_rel_def";
val _ = emit "state_rel_dec_clock_typed" "state_rel_dec_clock";
val _ = emit "state_rel_get_var_imm_typed" "state_rel_get_var_imm";
val _ = emit "state_rel_read_fp_reg_FLOOKUP_fp_regs_typed" "state_rel_read_fp_reg_FLOOKUP_fp_regs";
val _ = emit "state_rel_read_reg_FLOOKUP_regs_typed" "state_rel_read_reg_FLOOKUP_regs";
val _ = emit "state_rel_with_clock_typed" "state_rel_with_clock";
val _ = emit "state_rel_with_pc_typed" "state_rel_with_pc";
