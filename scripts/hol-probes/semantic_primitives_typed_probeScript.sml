(* Typed source declarations for semanticPrimitives (task 148). *)
load "preamble";
load "semanticPrimitivesTheory";
open HolKernel Parse boolLib bossLib;
open preamble semanticPrimitivesTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="semanticPrimitives",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by semanticPrimitives")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of semanticPrimitives")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "store_lookup_def_typed" "store_lookup_def";
val _ = emit "store_assign_def_typed" "store_assign_def";
val _ = dt_label "abort_typed" "abort";
val _ = dt_label "error_result_typed" "error_result";
val _ = dt_label "result_typed" "result";
val _ = dt_label "sem_env_typed" "sem_env";
val _ = dt_label "stamp_typed" "stamp";
val _ = dt_label "store_v_typed" "store_v";
val _ = dt_label "v_typed" "v";
val _ = emit "bind_exn_v_def_typed" "bind_exn_v_def";
val _ = emit "bind_stamp_def_typed" "bind_stamp_def";
val _ = emit "chr_exn_v_def_typed" "chr_exn_v_def";
val _ = emit "chr_stamp_def_typed" "chr_stamp_def";
val _ = emit "div_exn_v_def_typed" "div_exn_v_def";
val _ = emit "div_stamp_def_typed" "div_stamp_def";
val _ = emit "empty_store_def_typed" "empty_store_def";
val _ = emit "store_alloc_def_typed" "store_alloc_def";
val _ = emit "store_v_same_type_def_typed" "store_v_same_type_def";
val _ = emit "sub_exn_v_def_typed" "sub_exn_v_def";
val _ = emit "subscript_stamp_def_typed" "subscript_stamp_def";
val _ = dt_label "eval_decs_state_typed" "eval_decs_state";
val _ = dt_label "eval_oracle_state_typed" "eval_oracle_state";
val _ = dt_label "eval_state_typed" "eval_state";
val _ = dt_label "state_typed" "state";
val _ = dt_label "match_result_typed" "match_result";
val _ = emit "bool_type_num_def_typed" "bool_type_num_def";
val _ = emit "Boolv_def_typed" "Boolv_def";
val _ = emit "build_conv_def_typed" "build_conv_def";
val _ = emit "build_rec_env_def_typed" "build_rec_env_def";
val _ = emit "ctor_same_type_def_typed" "ctor_same_type_def";
val _ = emit "do_con_check_def_typed" "do_con_check_def";
val _ = emit "find_recfun_def_typed" "find_recfun_def";
val _ = emit "lit_same_type_def_typed" "lit_same_type_def";
val _ = emit "one_con_check_def_typed" "one_con_check_def";
val _ = emit "same_ctor_def_typed" "same_ctor_def";
val _ = emit "same_type_def_typed" "same_type_def";
val _ = emit "can_pmatch_all_def_typed" "can_pmatch_all_def";
val _ = emit "pmatch_def_typed" "pmatch_def";
val _ = dt_label "eq_result_typed" "eq_result";
val _ = emit "do_eq_def_typed" "do_eq_def";
val _ = emit "do_opapp_def_typed" "do_opapp_def";
val _ = emit "id_type_num_def_typed" "id_type_num_def";
val _ = emit "list_to_v_def_typed" "list_to_v_def";
val _ = emit "list_type_num_def_typed" "list_type_num_def";
val _ = emit "maybe_all_list_def_typed" "maybe_all_list_def";
val _ = emit "maybe_to_v_def_typed" "maybe_to_v_def";
val _ = emit "nat_to_v_def_typed" "nat_to_v_def";
val _ = emit "option_type_num_def_typed" "option_type_num_def";
val _ = emit "v_to_char_list_def_typed" "v_to_char_list_def";
val _ = emit "v_to_id_def_typed" "v_to_id_def";
val _ = emit "v_to_list_def_typed" "v_to_list_def";
val _ = emit "v_to_word64_def_typed" "v_to_word64_def";
val _ = emit "v_to_word64_list_def_typed" "v_to_word64_list_def";
val _ = emit "v_to_word8_def_typed" "v_to_word8_def";
val _ = emit "v_to_word8_list_def_typed" "v_to_word8_list_def";
val _ = emit "vs_to_string_def_typed" "vs_to_string_def";
val _ = dt_label "dest_thunk_ret_typed" "dest_thunk_ret";
val _ = dt_label "exp_or_val_typed" "exp_or_val";
val _ = emit "bad_thunk_update_def_typed" "bad_thunk_update_def";
val _ = emit "dest_thunk_def_typed" "dest_thunk_def";
val _ = emit "thunk_op_def_typed" "thunk_op_def";
val _ = emit "update_thunk_def_typed" "update_thunk_def";
val _ = emit "xor_bytes_def_typed" "xor_bytes_def";
val _ = emit "do_app_def_typed" "do_app_def";
val _ = emit "add_decs_generation_def_typed" "add_decs_generation_def";
val _ = emit "add_env_generation_def_typed" "add_env_generation_def";
val _ = emit "declare_env_def_typed" "declare_env_def";
val _ = emit "lookup_env_def_typed" "lookup_env_def";
val _ = emit "reset_env_generation_def_typed" "reset_env_generation_def";
val _ = emit "concrete_v_def_typed" "concrete_v_def";
val _ = emit "compiler_agrees_def_typed" "compiler_agrees_def";
val _ = emit "do_eval_def_typed" "do_eval_def";
val _ = emit "build_constrs_def_typed" "build_constrs_def";
val _ = emit "build_tdefs_def_typed" "build_tdefs_def";
val _ = emit "check_dup_ctors_def_typed" "check_dup_ctors_def";
val _ = emit "combine_dec_result_def_typed" "combine_dec_result_def";
val _ = emit "do_if_def_typed" "do_if_def";
val _ = emit "do_log_def_typed" "do_log_def";
val _ = emit "extend_dec_env_def_typed" "extend_dec_env_def";
val _ = emit "chars_to_ws_def_typed" "chars_to_ws_def";
val _ = emit "copy_array_def_typed" "copy_array_def";
val _ = emit "ws_to_chars_def_typed" "ws_to_chars_def";
val _ = emit "check_type_def_typed" "check_type_def";
val _ = emit "dest_Litv_def_typed" "dest_Litv_def";
val _ = emit "shift64_lookup_def_typed" "shift64_lookup_def";
val _ = emit "shift8_lookup_def_typed" "shift8_lookup_def";
val _ = emit "int_cmp_def_typed" "int_cmp_def";
val _ = emit "num_cmp_def_typed" "num_cmp_def";
val _ = emit "str_cmp_def_typed" "str_cmp_def";
val _ = emit "do_test_def_typed" "do_test_def";
val _ = emit "the_Litv_IntLit_def_typed" "the_Litv_IntLit_def";
val _ = emit "the_Litv_Word8_def_typed" "the_Litv_Word8_def";
val _ = emit "the_Litv_Word64_def_typed" "the_Litv_Word64_def";
val _ = emit "the_Litv_Float64_def_typed" "the_Litv_Float64_def";
val _ = emit "the_Litv_Char_def_typed" "the_Litv_Char_def";
val _ = emit "do_conversion_def_typed" "do_conversion_def";
val _ = emit "the_Boolv_def_typed" "the_Boolv_def";
val _ = emit "do_arith_def_typed" "do_arith_def";
