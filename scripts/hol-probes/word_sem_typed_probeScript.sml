(* Typed source declarations for wordSem (task 148). *)
load "preamble";
load "wordSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble wordSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="wordSem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by wordSem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of wordSem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "mem_load_32_def_typed" "mem_load_32_def";
val _ = emit "mem_load_byte_aux_def_typed" "mem_load_byte_aux_def";
val _ = emit "mem_store_32_def_typed" "mem_store_32_def";
val _ = emit "mem_store_byte_aux_def_typed" "mem_store_byte_aux_def";
val _ = emit "the_words_def_typed" "the_words_def";
val _ = emit "write_bytearray_def_typed" "write_bytearray_def";
val _ = emit "dec_clock_def_typed" "dec_clock_def";
val _ = emit "fix_clock_def_typed" "fix_clock_def";
val _ = emit "flush_state_def_typed" "flush_state_def";
val _ = emit "get_fp_var_def_typed" "get_fp_var_def";
val _ = emit "get_store_def_typed" "get_store_def";
val _ = emit "get_var_def_typed" "get_var_def";
val _ = emit "get_var_imm_def_typed" "get_var_imm_def";
val _ = emit "get_vars_def_typed" "get_vars_def";
val _ = emit "mem_load_def_typed" "mem_load_def";
val _ = emit "mem_store_def_typed" "mem_store_def";
val _ = emit "set_fp_var_def_typed" "set_fp_var_def";
val _ = emit "set_store_def_typed" "set_store_def";
val _ = emit "set_var_def_typed" "set_var_def";
val _ = emit "set_vars_def_typed" "set_vars_def";
val _ = emit "unset_var_def_typed" "unset_var_def";
val _ = emit "word_exp_def_typed" "word_exp_def";
val _ = emit "get_word_def_typed" "get_word_def";
val _ = emit "is_fwd_ptr_def_typed" "is_fwd_ptr_def";
val _ = emit "is_word_def_typed" "is_word_def";
val _ = emit "isWord_def_typed" "isWord_def";
val _ = emit "theWord_def_typed" "theWord_def";
val _ = emit "word_cmp_def_typed" "word_cmp_def";
val _ = emit "alloc_def_typed" "alloc_def";
val _ = emit "assign_def_typed" "assign_def";
val _ = emit "gc_def_typed" "gc_def";
val _ = emit "has_space_def_typed" "has_space_def";
val _ = emit "dec_stack_def_typed" "dec_stack_def";
val _ = emit "enc_stack_def_typed" "enc_stack_def";
val _ = emit "find_code_def_typed" "find_code_def";
val _ = emit "add_ret_loc_def_typed" "add_ret_loc_def";
val _ = emit "bad_dest_args_def_typed" "bad_dest_args_def";
val _ = emit "bad_fun_return_def_typed" "bad_fun_return_def";
val _ = emit "const_addresses_def_typed" "const_addresses_def";
val _ = emit "const_writes_def_typed" "const_writes_def";
val _ = emit "cont_loop_def_typed" "cont_loop_def";
val _ = emit "exit_loop_def_typed" "exit_loop_def";
val _ = emit "MustTerminate_limit_def_typed" "MustTerminate_limit_def";
val _ = emit "STOP_def_typed" "STOP_def";
val _ = emit "call_env_def_typed" "call_env_def";
val _ = emit "cut_state_def_typed" "cut_state_def";
val _ = emit "cut_state_opt_def_typed" "cut_state_opt_def";
val _ = emit "jump_exc_def_typed" "jump_exc_def";
val _ = emit "pop_env_def_typed" "pop_env_def";
val _ = emit "push_env_def_typed" "push_env_def";
val _ = emit "cut_env_def_typed" "cut_env_def";
val _ = emit "cut_envs_def_typed" "cut_envs_def";
val _ = emit "cut_names_def_typed" "cut_names_def";
val _ = emit "env_to_list_def_typed" "env_to_list_def";
val _ = emit "key_val_compare_def_typed" "key_val_compare_def";
val _ = emit "list_rearrange_def_typed" "list_rearrange_def";
val _ = emit "evaluate_def_typed" "evaluate_def";
val _ = emit "alloc_clock_typed" "alloc_clock";
val _ = emit "evaluate_clock_typed" "evaluate_clock";
val _ = emit "gc_clock_typed" "gc_clock";
val _ = emit "sh_mem_set_var_clock_typed" "sh_mem_set_var_clock";
val _ = emit "share_inst_clock_typed" "share_inst_clock";
val _ = emit "evaluate_ind_typed" "evaluate_ind";
val _ = emit "inst_def_typed" "inst_def";
val _ = emit "semantics_def_typed" "semantics_def";
val _ = emit "word_lang_safe_for_space_def_typed" "word_lang_safe_for_space_def";
val _ = emit "sh_mem_load_def_typed" "sh_mem_load_def";
val _ = emit "sh_mem_load16_def_typed" "sh_mem_load16_def";
val _ = emit "sh_mem_load32_def_typed" "sh_mem_load32_def";
val _ = emit "sh_mem_load_byte_def_typed" "sh_mem_load_byte_def";
val _ = emit "sh_mem_set_var_def_typed" "sh_mem_set_var_def";
val _ = emit "sh_mem_store_def_typed" "sh_mem_store_def";
val _ = emit "sh_mem_store16_def_typed" "sh_mem_store16_def";
val _ = emit "sh_mem_store32_def_typed" "sh_mem_store32_def";
val _ = emit "sh_mem_store_byte_def_typed" "sh_mem_store_byte_def";
val _ = emit "share_inst_def_typed" "share_inst_def";
val _ = dt_label "buffer_typed" "buffer";
val _ = dt_label "result_typed" "result";
val _ = dt_label "stack_frame_typed" "stack_frame";
val _ = dt_label "state_typed" "state";
val _ = emit "buffer_flush_def_typed" "buffer_flush_def";
val _ = emit "buffer_write_def_typed" "buffer_write_def";
val _ = emit "isException_def_typed" "isException_def";
val _ = emit "isResult_def_typed" "isResult_def";
val _ = emit "stack_size_def_typed" "stack_size_def";
val _ = emit "stack_size_frame_def_typed" "stack_size_frame_def";
