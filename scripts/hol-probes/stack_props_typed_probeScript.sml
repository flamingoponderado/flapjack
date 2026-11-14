(* Typed source declarations for stackProps (task 148). *)
load "preamble";
load "stackPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble stackPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stackProps",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stackProps")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stackProps")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "addr_ok_def_typed" "addr_ok_def";
val _ = emit "addr_name_def_typed" "addr_name_def";
val _ = emit "alloc_arg_def_typed" "alloc_arg_def";
val _ = emit "alloc_const_typed" "alloc_const";
val _ = emit "alloc_with_const_typed" "alloc_with_const";
val _ = emit "gc_with_const_typed" "gc_with_const";
val _ = emit "store_const_sem_const_typed" "store_const_sem_const";
val _ = emit "store_const_sem_with_const_typed" "store_const_sem_with_const";
val _ = emit "arith_name_def_typed" "arith_name_def";
val _ = emit "call_args_def_typed" "call_args_def";
val _ = emit "bad_fun_return_IMP_typed" "bad_fun_return_IMP";
val _ = emit "clock_neutral_def_typed" "clock_neutral_def";
val _ = emit "cont_loop_IMP_typed" "cont_loop_IMP";
val _ = emit "dec_clock_const_typed" "dec_clock_const";
val _ = emit "pair_map_eq_typed" "pair_map_eq";
val _ = emit "with_clock_ffi_typed" "with_clock_ffi";
val _ = emit "get_code_labels_def_typed" "get_code_labels_def";
val _ = emit "stack_get_handler_labels_def_typed" "stack_get_handler_labels_def";
val _ = emit "evaluate_add_clock_typed" "evaluate_add_clock";
val _ = emit "evaluate_add_clock_io_events_mono_typed" "evaluate_add_clock_io_events_mono";
val _ = emit "evaluate_code_bitmaps_typed" "evaluate_code_bitmaps";
val _ = emit "evaluate_consts_typed" "evaluate_consts";
val _ = emit "evaluate_io_events_mono_typed" "evaluate_io_events_mono";
val _ = emit "evaluate_mono_typed" "evaluate_mono";
val _ = emit "evaluate_clock_neutral_typed" "evaluate_clock_neutral";
val _ = emit "evaluate_ffi_neutral_typed" "evaluate_ffi_neutral";
val _ = emit "assign_with_const_typed" "assign_with_const";
val _ = emit "mem_load_with_const_typed" "mem_load_with_const";
val _ = emit "word_exp_with_const_typed" "word_exp_with_const";
val _ = emit "fixed_names_def_typed" "fixed_names_def";
val _ = emit "fp_name_def_typed" "fp_name_def";
val _ = emit "no_install_def_typed" "no_install_def";
val _ = emit "no_shmemop_def_typed" "no_shmemop_def";
val _ = emit "inst_const_typed" "inst_const";
val _ = emit "inst_with_const_typed" "inst_with_const";
val _ = emit "inst_name_def_typed" "inst_name_def";
val _ = emit "stack_good_code_labels_def_typed" "stack_good_code_labels_def";
val _ = emit "stack_good_handler_labels_def_typed" "stack_good_handler_labels_def";
val _ = emit "extract_labels_def_typed" "extract_labels_def";
val _ = emit "find_code_IMP_get_labels_typed" "find_code_IMP_get_labels";
val _ = emit "stack_asm_name_def_typed" "stack_asm_name_def";
val _ = emit "stack_asm_ok_def_typed" "stack_asm_ok_def";
val _ = emit "reg_bound_def_typed" "reg_bound_def";
val _ = emit "reg_bound_exp_def_typed" "reg_bound_exp_def";
val _ = emit "reg_bound_inst_def_typed" "reg_bound_inst_def";
val _ = emit "reg_imm_name_def_typed" "reg_imm_name_def";
val _ = emit "reg_name_def_typed" "reg_name_def";
val _ = emit "stack_asm_remove_def_typed" "stack_asm_remove_def";
val _ = emit "sh_mem_load16_with_const_typed" "sh_mem_load16_with_const";
val _ = emit "sh_mem_load32_with_const_typed" "sh_mem_load32_with_const";
val _ = emit "sh_mem_load_byte_with_const_typed" "sh_mem_load_byte_with_const";
val _ = emit "sh_mem_load_with_const_typed" "sh_mem_load_with_const";
val _ = emit "sh_mem_op_const_typed" "sh_mem_op_const";
val _ = emit "sh_mem_store16_with_const_typed" "sh_mem_store16_with_const";
val _ = emit "sh_mem_store32_with_const_typed" "sh_mem_store32_with_const";
val _ = emit "sh_mem_store_byte_with_const_typed" "sh_mem_store_byte_with_const";
val _ = emit "sh_mem_store_with_const_typed" "sh_mem_store_with_const";
val _ = emit "dec_stack_length_typed" "dec_stack_length";
val _ = emit "map_bitmap_length_typed" "map_bitmap_length";
val _ = emit "empty_env_const_typed" "empty_env_const";
val _ = emit "empty_env_with_const_typed" "empty_env_with_const";
val _ = emit "get_var_imm_with_const_typed" "get_var_imm_with_const";
val _ = emit "get_var_with_const_typed" "get_var_with_const";
val _ = emit "set_fp_var_const_typed" "set_fp_var_const";
val _ = emit "set_store_const_typed" "set_store_const";
val _ = emit "set_store_with_const_typed" "set_store_with_const";
val _ = emit "set_var_const_typed" "set_var_const";
val _ = emit "set_var_with_const_typed" "set_var_with_const";
