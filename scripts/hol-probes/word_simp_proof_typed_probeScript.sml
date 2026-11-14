(* Typed source declarations for word_simpProof (task 148). *)
load "preamble";
load "word_simpProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_simpProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_simpProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_simpProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_simpProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "compile_exp_thm_typed" "compile_exp_thm";
val _ = emit "evaluate_simp_duplicate_if_typed" "evaluate_simp_duplicate_if";
val _ = emit "evaluate_simp_push_out_if_typed" "evaluate_simp_push_out_if";
val _ = emit "evaluate_const_fp_typed" "evaluate_const_fp";
val _ = emit "evaluate_const_fp_loop_typed" "evaluate_const_fp_loop";
val _ = emit "evaluate_drop_consts_typed" "evaluate_drop_consts";
val _ = emit "evaluate_drop_consts_1_typed" "evaluate_drop_consts_1";
val _ = emit "get_var_set_vars_ignore_typed" "get_var_set_vars_ignore";
val _ = emit "LIST_REL_append_left_typed" "LIST_REL_append_left";
val _ = emit "LIST_REL_prefix_typed" "LIST_REL_prefix";
val _ = emit "const_fp_exp_word_exp_typed" "const_fp_exp_word_exp";
val _ = emit "const_fp_exp_word_exp_const_typed" "const_fp_exp_word_exp_const";
val _ = emit "cs_delete_if_set_typed" "cs_delete_if_set";
val _ = emit "cs_delete_if_set_x2_typed" "cs_delete_if_set_x2";
val _ = emit "gc_fun_const_ok_def_typed" "gc_fun_const_ok_def";
val _ = emit "get_var_imm_cs_imp_get_var_imm_typed" "get_var_imm_cs_imp_get_var_imm";
val _ = emit "get_var_mem_store_thm_typed" "get_var_mem_store_thm";
val _ = emit "get_var_move_thm_typed" "get_var_move_thm";
val _ = emit "get_var_set_var_thm_typed" "get_var_set_var_thm";
val _ = emit "lookup_const_fp_move_cs_typed" "lookup_const_fp_move_cs";
val _ = emit "lookup_const_fp_move_cs_NONE_typed" "lookup_const_fp_move_cs_NONE";
val _ = emit "lookup_const_fp_move_cs_SOME_typed" "lookup_const_fp_move_cs_SOME";
val _ = emit "lookup_const_fp_move_cs_SOME_part_typed" "lookup_const_fp_move_cs_SOME_part";
val _ = emit "lookup_filter_v_SOME_typed" "lookup_filter_v_SOME";
val _ = emit "lookup_filter_v_SOME_imp_typed" "lookup_filter_v_SOME_imp";
val _ = emit "lookup_inter_eq_some_typed" "lookup_inter_eq_some";
val _ = emit "push_env_set_store_stack_typed" "push_env_set_store_stack";
val _ = emit "set_vars_move_NONE_typed" "set_vars_move_NONE";
val _ = emit "set_vars_move_SOME_typed" "set_vars_move_SOME";
val _ = emit "sf_gc_consts_def_typed" "sf_gc_consts_def";
val _ = emit "sf_gc_consts_refl_typed" "sf_gc_consts_refl";
val _ = emit "sf_gc_consts_trans_typed" "sf_gc_consts_trans";
val _ = emit "strip_const_thm_typed" "strip_const_thm";
val _ = emit "the_words_thm_typed" "the_words_thm";
val _ = emit "ALL_DISTINCT_PERM_FST_typed" "ALL_DISTINCT_PERM_FST";
val _ = emit "ALOOKUP_ALL_DISTINCT_FST_PERM_typed" "ALOOKUP_ALL_DISTINCT_FST_PERM";
val _ = emit "ALOOKUP_ALL_DISTINCT_FST_PERM_SOME_typed" "ALOOKUP_ALL_DISTINCT_FST_PERM_SOME";
val _ = emit "ALOOKUP_LIST_REL_sf_gc_consts_typed" "ALOOKUP_LIST_REL_sf_gc_consts";
val _ = emit "ALOOKUP_LIST_REL_sf_gc_consts_NONE_typed" "ALOOKUP_LIST_REL_sf_gc_consts_NONE";
val _ = emit "ALOOKUP_LIST_REL_value_rel_typed" "ALOOKUP_LIST_REL_value_rel";
val _ = emit "EVERY2_trans_LASTN_sf_gc_consts_typed" "EVERY2_trans_LASTN_sf_gc_consts";
val _ = emit "HD_LASTN_typed" "HD_LASTN";
val _ = emit "LASTN_LENGTH_CONS_typed" "LASTN_LENGTH_CONS";
val _ = emit "LASTN_TL_res_typed" "LASTN_TL_res";
val _ = emit "LIST_REL_call_Result_typed" "LIST_REL_call_Result";
val _ = emit "LIST_REL_push_env_typed" "LIST_REL_push_env";
val _ = emit "call_env_push_env_dec_clock_handler_length_typed" "call_env_push_env_dec_clock_handler_length";
val _ = emit "enc_stack_dec_stack_is_gc_word_const_typed" "enc_stack_dec_stack_is_gc_word_const";
val _ = emit "evaluate_gc_fun_const_ok_typed" "evaluate_gc_fun_const_ok";
val _ = emit "evaluate_sf_gc_consts_typed" "evaluate_sf_gc_consts";
val _ = emit "gc_fun_sf_gc_consts_typed" "gc_fun_sf_gc_consts";
val _ = emit "gc_handler_typed" "gc_handler";
val _ = emit "gc_sf_gc_consts_typed" "gc_sf_gc_consts";
val _ = emit "get_above_handler_def_typed" "get_above_handler_def";
val _ = emit "get_above_handler_call_env_push_env_dec_clock_typed" "get_above_handler_call_env_push_env_dec_clock";
val _ = emit "pop_env_gc_fun_typed" "pop_env_gc_fun";
val _ = emit "pop_env_gc_fun_const_ok_typed" "pop_env_gc_fun_const_ok";
val _ = emit "push_env_pop_env_locals_thm_typed" "push_env_pop_env_locals_thm";
val _ = emit "sf_gc_consts_get_above_handler_typed" "sf_gc_consts_get_above_handler";
val _ = emit "is_gc_word_const_def_typed" "is_gc_word_const_def";
val _ = emit "dest_If_Eq_Imm_thm_typed" "dest_If_Eq_Imm_thm";
val _ = emit "dest_If_thm_typed" "dest_If_thm";
val _ = emit "dest_Seq_Assign_Const_IMP_typed" "dest_Seq_Assign_Const_IMP";
val _ = emit "dest_Seq_IMP_typed" "dest_Seq_IMP";
val _ = emit "evaluate_Loop_body_cong_typed" "evaluate_Loop_body_cong";
val _ = emit "evaluate_Loop_body_cong_gc_typed" "evaluate_Loop_body_cong_gc";
val _ = emit "evaluate_Seq_Skip_typed" "evaluate_Seq_Skip";
val _ = emit "evaluate_Seq_assoc_typed" "evaluate_Seq_assoc";
val _ = emit "evaluate_Seq_assoc_lemma_typed" "evaluate_Seq_assoc_lemma";
val _ = emit "evaluate_Skip_Seq_typed" "evaluate_Skip_Seq";
val _ = emit "evaluate_SmartSeq_typed" "evaluate_SmartSeq";
