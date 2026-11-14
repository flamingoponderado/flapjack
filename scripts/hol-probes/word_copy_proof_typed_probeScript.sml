(* Typed source declarations for word_copyProof (task 148). *)
load "preamble";
load "word_copyProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_copyProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_copyProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_copyProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_copyProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "copy_prop_correct_typed" "copy_prop_correct";
val _ = emit "evaluate_copy_prop_typed" "evaluate_copy_prop";
val _ = emit "copy_prop_inst_correct_typed" "copy_prop_inst_correct";
val _ = emit "copy_prop_inst_eval_typed" "copy_prop_inst_eval";
val _ = emit "both_alloc_vars_def_typed" "both_alloc_vars_def";
val _ = emit "CPstate_inv_def_typed" "CPstate_inv_def";
val _ = emit "empty_eq_inv_typed" "empty_eq_inv";
val _ = emit "lookup_eqI_typed" "lookup_eqI";
val _ = emit "lookup_eq_remove_eq_t_typed" "lookup_eq_remove_eq_t";
val _ = emit "lookup_eq_set_eqD_typed" "lookup_eq_set_eqD";
val _ = emit "lookup_eq_set_eq_is_alloc_var1_typed" "lookup_eq_set_eq_is_alloc_var1";
val _ = emit "lookup_eq_set_eq_is_alloc_var2_typed" "lookup_eq_set_eq_is_alloc_var2";
val _ = emit "lookup_eq_set_eq_not_alloc_var_typed" "lookup_eq_set_eq_not_alloc_var";
val _ = emit "lookup_eq_set_eq_s_typed" "lookup_eq_set_eq_s";
val _ = emit "lookup_eq_set_eq_t_typed" "lookup_eq_set_eq_t";
val _ = emit "lookup_store_eq_set_eqD_typed" "lookup_store_eq_set_eqD";
val _ = emit "merge_eqs_inv_typed" "merge_eqs_inv";
val _ = emit "remove_eq_inv_typed" "remove_eq_inv";
val _ = emit "remove_eqs_inv_typed" "remove_eqs_inv";
val _ = emit "same_classD_typed" "same_classD";
val _ = emit "set_eq_inv_typed" "set_eq_inv";
val _ = emit "set_eq_store_to_eq_typed" "set_eq_store_to_eq";
val _ = emit "set_store_eq_inv_typed" "set_store_eq_inv";
val _ = emit "CPstate_model_typed" "CPstate_model";
val _ = emit "CPstate_models_def_typed" "CPstate_models_def";
val _ = emit "CPstate_modelsD_typed" "CPstate_modelsD";
val _ = emit "CPstate_modelsI_typed" "CPstate_modelsI";
val _ = emit "CPstate_models_same_typed" "CPstate_models_same";
val _ = emit "CPstate_models_with_const_typed" "CPstate_models_with_const";
val _ = emit "merge_eqs_model1_typed" "merge_eqs_model1";
val _ = emit "merge_eqs_model2_typed" "merge_eqs_model2";
val _ = emit "remove_eq_model_typed" "remove_eq_model";
val _ = emit "remove_eq_model_insert_typed" "remove_eq_model_insert";
val _ = emit "remove_eq_model_set_var_typed" "remove_eq_model_set_var";
val _ = emit "set_fp_var_model_typed" "set_fp_var_model";
val _ = emit "copy_prop_inst_inv_typed" "copy_prop_inst_inv";
val _ = emit "copy_prop_move_eval_typed" "copy_prop_move_eval";
val _ = emit "copy_prop_move_eval_aux1_typed" "copy_prop_move_eval_aux1";
val _ = emit "copy_prop_move_eval_aux2_typed" "copy_prop_move_eval_aux2";
val _ = emit "copy_prop_move_eval_aux3_typed" "copy_prop_move_eval_aux3";
val _ = emit "copy_prop_move_get_vars_typed" "copy_prop_move_get_vars";
val _ = emit "copy_prop_move_inv_typed" "copy_prop_move_inv";
val _ = emit "copy_prop_move_model_aux_typed" "copy_prop_move_model_aux";
val _ = emit "copy_prop_prog_inv_typed" "copy_prop_prog_inv";
val _ = emit "CPstate_modelsD_get_var_typed" "CPstate_modelsD_get_var";
val _ = emit "CPstate_modelsD_get_var_imm_typed" "CPstate_modelsD_get_var_imm";
val _ = emit "CPstate_modelsD_get_vars_typed" "CPstate_modelsD_get_vars";
val _ = emit "CPstate_modelsD_lookup_eq_imm_typed" "CPstate_modelsD_lookup_eq_imm";
val _ = emit "CPstate_modelsD_Var_typed" "CPstate_modelsD_Var";
val _ = emit "empty_eq_model_typed" "empty_eq_model";
val _ = emit "lookup_alist_insert_same_typed" "lookup_alist_insert_same";
val _ = emit "lookup_eq_idempotent_typed" "lookup_eq_idempotent";
val _ = emit "MAP_get_var_eqD_typed" "MAP_get_var_eqD";
val _ = emit "set_eq_remove_eq_models_typed" "set_eq_remove_eq_models";
val _ = emit "copy_prop_move_correct_typed" "copy_prop_move_correct";
val _ = emit "copy_prop_move_model_typed" "copy_prop_move_model";
val _ = emit "CPstate_modelsD_copy_prop_share_typed" "CPstate_modelsD_copy_prop_share";
val _ = emit "evaluate_Loop_body_cong_err_typed" "evaluate_Loop_body_cong_err";
val _ = emit "EVERY_NOT_MEM_D_typed" "EVERY_NOT_MEM_D";
val _ = emit "lookup_eq_remove_t_same_typed" "lookup_eq_remove_t_same";
val _ = emit "lookup_eq_set_store_eq_typed" "lookup_eq_set_store_eq";
val _ = emit "lookup_remove_eq_typed" "lookup_remove_eq";
val _ = emit "lookup_store_eq_set_store_eq_1_typed" "lookup_store_eq_set_store_eq_1";
val _ = emit "lookup_store_eq_set_store_eq_2_typed" "lookup_store_eq_set_store_eq_2";
val _ = emit "lookup_store_eq_set_store_eq_same_typed" "lookup_store_eq_set_store_eq_same";
val _ = emit "lookup_store_eq_SOME_typed" "lookup_store_eq_SOME";
val _ = emit "remove_eq_comm_typed" "remove_eq_comm";
val _ = emit "remove_eq_model_unset_var_typed" "remove_eq_model_unset_var";
val _ = emit "set_store_eq_model_set_store_typed" "set_store_eq_model_set_store";
val _ = emit "set_store_eq_model_set_var_typed" "set_store_eq_model_set_var";
val _ = emit "word_exp_cong_Load_typed" "word_exp_cong_Load";
val _ = emit "word_exp_cong_Op_typed" "word_exp_cong_Op";
val _ = emit "word_exp_cong_Shift_typed" "word_exp_cong_Shift";
val _ = emit "word_exp_cong_Var_typed" "word_exp_cong_Var";
