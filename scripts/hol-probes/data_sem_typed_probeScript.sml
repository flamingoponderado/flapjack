(* Typed source declarations for dataSem (task 148). *)
load "preamble";
load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble dataSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="dataSem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by dataSem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of dataSem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "do_app_def_typed" "do_app_def";
val _ = emit "do_install_def_typed" "do_install_def";
val _ = emit "do_app_aux_def_typed" "do_app_aux_def";
val _ = emit "do_build_def_typed" "do_build_def";
val _ = emit "do_build_const_def_typed" "do_build_const_def";
val _ = emit "do_part_def_typed" "do_part_def";
val _ = emit "list_to_v_def_typed" "list_to_v_def";
val _ = emit "with_fresh_ts_def_typed" "with_fresh_ts_def";
val _ = dt_label "dest_thunk_ret_typed" "dest_thunk_ret";
val _ = emit "allowed_op_def_typed" "allowed_op_def";
val _ = emit "bad_thunk_update_def_typed" "bad_thunk_update_def";
val _ = emit "call_env_def_typed" "call_env_def";
val _ = emit "cut_env_def_typed" "cut_env_def";
val _ = emit "cut_state_def_typed" "cut_state_def";
val _ = emit "cut_state_opt_def_typed" "cut_state_opt_def";
val _ = emit "dest_Boolv_def_typed" "dest_Boolv_def";
val _ = emit "dest_thunk_def_typed" "dest_thunk_def";
val _ = emit "find_code_def_typed" "find_code_def";
val _ = emit "flush_state_def_typed" "flush_state_def";
val _ = emit "install_sfs_def_typed" "install_sfs_def";
val _ = emit "isBool_def_typed" "isBool_def";
val _ = emit "jump_exc_def_typed" "jump_exc_def";
val _ = emit "pop_env_def_typed" "pop_env_def";
val _ = emit "push_env_def_typed" "push_env_def";
val _ = emit "set_vars_def_typed" "set_vars_def";
val _ = emit "size_of_stack_def_typed" "size_of_stack_def";
val _ = emit "size_of_stack_frame_def_typed" "size_of_stack_frame_def";
val _ = emit "v_to_bytes_def_typed" "v_to_bytes_def";
val _ = emit "v_to_words_def_typed" "v_to_words_def";
val _ = emit "do_eq_def_typed" "do_eq_def";
val _ = emit "isClos_def_typed" "isClos_def";
val _ = emit "evaluate_def_typed" "evaluate_def";
val _ = emit "finalise_cons_def_typed" "finalise_cons_def";
val _ = emit "add_space_def_typed" "add_space_def";
val _ = emit "bignum_digits_def_typed" "bignum_digits_def";
val _ = emit "bignum_size_def_typed" "bignum_size_def";
val _ = emit "check_res_def_typed" "check_res_def";
val _ = emit "check_res_IMP_typed" "check_res_IMP";
val _ = emit "consume_space_def_typed" "consume_space_def";
val _ = emit "extract_stack_def_typed" "extract_stack_def";
val _ = emit "global_to_vs_def_typed" "global_to_vs_def";
val _ = emit "no_thunks_in_refs_def_typed" "no_thunks_in_refs_def";
val _ = emit "size_of_heap_def_typed" "size_of_heap_def";
val _ = emit "size_of_heap_args_def_typed" "size_of_heap_args_def";
val _ = emit "size_of_def_typed" "size_of_def";
val _ = emit "stack_to_vs_def_typed" "stack_to_vs_def";
val _ = emit "do_int_app_def_typed" "do_int_app_def";
val _ = emit "check_lim_def_typed" "check_lim_def";
val _ = emit "do_lim_safe_typed" "do_lim_safe";
val _ = emit "lim_safe_def_typed" "lim_safe_def";
val _ = emit "lim_safe_part_def_typed" "lim_safe_part_def";
val _ = emit "compute_limits_def_typed" "compute_limits_def";
val _ = emit "data_lang_safe_for_space_def_typed" "data_lang_safe_for_space_def";
val _ = emit "evaluate_peak_def_typed" "evaluate_peak_def";
val _ = emit "evaluate_safe_def_typed" "evaluate_safe_def";
val _ = emit "semantics_def_typed" "semantics_def";
val _ = emit "do_space_def_typed" "do_space_def";
val _ = emit "space_consumed_def_typed" "space_consumed_def";
val _ = emit "do_stack_def_typed" "do_stack_def";
val _ = emit "evaluate_clock_typed" "evaluate_clock";
val _ = emit "fix_clock_evaluate_typed" "fix_clock_evaluate";
val _ = emit "do_app_clock_typed" "do_app_clock";
val _ = emit "do_stack_clock_typed" "do_stack_clock";
val _ = emit "eq_code_stack_max_def_typed" "eq_code_stack_max_def";
val _ = emit "stack_consumed_def_typed" "stack_consumed_def";
val _ = emit "vb_size_def_typed" "vb_size_def";
val _ = emit "vs_depth_def_typed" "vs_depth_def";
val _ = dt_label "limits_typed" "limits";
val _ = dt_label "stack_typed" "stack";
val _ = dt_label "state_typed" "state";
val _ = emit "arch_size_def_typed" "arch_size_def";
val _ = emit "dec_clock_def_typed" "dec_clock_def";
val _ = emit "fix_clock_def_typed" "fix_clock_def";
val _ = emit "get_var_def_typed" "get_var_def";
val _ = emit "get_vars_def_typed" "get_vars_def";
val _ = emit "initial_state_def_typed" "initial_state_def";
val _ = emit "set_var_def_typed" "set_var_def";
val _ = emit "small_num_def_typed" "small_num_def";
val _ = dt_label "v_typed" "v";
val _ = emit "Boolv_def_typed" "Boolv_def";
val _ = emit "Unit_def_typed" "Unit_def";
val _ = emit "v_to_list_def_typed" "v_to_list_def";
val _ = emit "do_word_app_def_typed" "do_word_app_def";
