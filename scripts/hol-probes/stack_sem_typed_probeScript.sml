(* Typed source declarations for stackSem (task 148). *)
load "preamble";
load "stackSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble stackSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stackSem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stackSem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stackSem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "alloc_def_typed" "alloc_def";
val _ = emit "gc_def_typed" "gc_def";
val _ = emit "has_space_def_typed" "has_space_def";
val _ = emit "filter_bitmap_def_typed" "filter_bitmap_def";
val _ = emit "filter_bitmap_LENGTH_typed" "filter_bitmap_LENGTH";
val _ = emit "map_bitmap_def_typed" "map_bitmap_def";
val _ = emit "map_bitmap_LENGTH_typed" "map_bitmap_LENGTH";
val _ = emit "alloc_clock_typed" "alloc_clock";
val _ = emit "gc_clock_typed" "gc_clock";
val _ = emit "store_const_sem_clock_typed" "store_const_sem_clock";
val _ = emit "evaluate_clock_typed" "evaluate_clock";
val _ = emit "bad_fun_return_def_typed" "bad_fun_return_def";
val _ = emit "cont_loop_def_typed" "cont_loop_def";
val _ = emit "dest_Seq_def_typed" "dest_Seq_def";
val _ = emit "exit_loop_def_typed" "exit_loop_def";
val _ = emit "find_code_def_typed" "find_code_def";
val _ = emit "fix_clock_def_typed" "fix_clock_def";
val _ = emit "fix_clock_evaluate_typed" "fix_clock_evaluate";
val _ = emit "evaluate_def_typed" "evaluate_def";
val _ = emit "assign_def_typed" "assign_def";
val _ = emit "word_exp_def_typed" "word_exp_def";
val _ = emit "inst_def_typed" "inst_def";
val _ = emit "get_labels_def_typed" "get_labels_def";
val _ = emit "loc_check_def_typed" "loc_check_def";
val _ = emit "semantics_def_typed" "semantics_def";
val _ = emit "sh_mem_load_def_typed" "sh_mem_load_def";
val _ = emit "sh_mem_load16_def_typed" "sh_mem_load16_def";
val _ = emit "sh_mem_load32_def_typed" "sh_mem_load32_def";
val _ = emit "sh_mem_load_byte_def_typed" "sh_mem_load_byte_def";
val _ = emit "sh_mem_op_def_typed" "sh_mem_op_def";
val _ = emit "sh_mem_store_def_typed" "sh_mem_store_def";
val _ = emit "sh_mem_store16_def_typed" "sh_mem_store16_def";
val _ = emit "sh_mem_store32_def_typed" "sh_mem_store32_def";
val _ = emit "sh_mem_store_byte_def_typed" "sh_mem_store_byte_def";
val _ = emit "dec_stack_def_typed" "dec_stack_def";
val _ = emit "enc_stack_def_typed" "enc_stack_def";
val _ = emit "full_read_bitmap_def_typed" "full_read_bitmap_def";
val _ = dt_label "result_typed" "result";
val _ = dt_label "state_typed" "state";
val _ = emit "dec_clock_def_typed" "dec_clock_def";
val _ = emit "empty_env_def_typed" "empty_env_def";
val _ = emit "get_fp_var_def_typed" "get_fp_var_def";
val _ = emit "get_var_def_typed" "get_var_def";
val _ = emit "get_var_imm_def_typed" "get_var_imm_def";
val _ = emit "get_vars_def_typed" "get_vars_def";
val _ = emit "mem_load_def_typed" "mem_load_def";
val _ = emit "mem_store_def_typed" "mem_store_def";
val _ = emit "set_fp_var_def_typed" "set_fp_var_def";
val _ = emit "set_store_def_typed" "set_store_def";
val _ = emit "set_var_def_typed" "set_var_def";
val _ = emit "copy_words_def_typed" "copy_words_def";
val _ = emit "copy_words_for_pattern_def_typed" "copy_words_for_pattern_def";
val _ = emit "copy_words_for_pattern_LESS_EQ_typed" "copy_words_for_pattern_LESS_EQ";
val _ = emit "store_const_sem_def_typed" "store_const_sem_def";
val _ = emit "check_store_consts_opt_def_typed" "check_store_consts_opt_def";
val _ = emit "bit_length_def_typed" "bit_length_def";
val _ = emit "read_bitmap_def_typed" "read_bitmap_def";
