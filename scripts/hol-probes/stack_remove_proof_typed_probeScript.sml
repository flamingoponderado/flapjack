(* Typed source declarations for stack_removeProof (task 148). *)
load "preamble";
load "stack_removeProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble stack_removeProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stack_removeProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stack_removeProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stack_removeProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "addresses_def_typed" "addresses_def";
val _ = emit "addresses_thm_typed" "addresses_thm";
val _ = emit "call_FFI_LENGTH_typed" "call_FFI_LENGTH";
val _ = emit "is_SOME_Word_def_typed" "is_SOME_Word_def";
val _ = emit "LENGTH_read_mem_typed" "LENGTH_read_mem";
val _ = emit "read_mem_def_typed" "read_mem_def";
val _ = emit "the_SOME_Word_def_typed" "the_SOME_Word_def";
val _ = emit "stack_remove_comp_stack_asm_name_typed" "stack_remove_comp_stack_asm_name";
val _ = emit "stack_remove_stack_asm_name_typed" "stack_remove_stack_asm_name";
val _ = emit "stack_remove_call_args_typed" "stack_remove_call_args";
val _ = emit "code_rel_def_typed" "code_rel_def";
val _ = emit "compile_semantics_typed" "compile_semantics";
val _ = emit "copy_each_thm_typed" "copy_each_thm";
val _ = emit "copy_loop_thm_typed" "copy_loop_thm";
val _ = emit "state_rel_word_exp_typed" "state_rel_word_exp";
val _ = emit "make_init_any_bitmaps_typed" "make_init_any_bitmaps";
val _ = emit "make_init_any_code_typed" "make_init_any_code";
val _ = emit "make_init_any_compile_oracle_typed" "make_init_any_compile_oracle";
val _ = emit "make_init_any_stack_limit_typed" "make_init_any_stack_limit";
val _ = emit "make_init_any_use_alloc_typed" "make_init_any_use_alloc";
val _ = emit "make_init_any_use_stack_typed" "make_init_any_use_stack";
val _ = emit "make_init_any_use_store_typed" "make_init_any_use_store";
val _ = emit "clock_neutral_store_list_code_typed" "clock_neutral_store_list_code";
val _ = emit "init_code_thm_typed" "init_code_thm";
val _ = emit "init_code_pre_def_typed" "init_code_pre_def";
val _ = emit "evaluate_init_code_ffi_typed" "evaluate_init_code_ffi";
val _ = emit "make_init_any_ffi_typed" "make_init_any_ffi";
val _ = emit "get_stack_heap_limit_def_typed" "get_stack_heap_limit_def";
val _ = emit "read_pointers_def_typed" "read_pointers_def";
val _ = emit "discharge_these_def_typed" "discharge_these_def";
val _ = emit "init_pre_def_typed" "init_pre_def";
val _ = emit "make_init_any_def_typed" "make_init_any_def";
val _ = emit "make_init_opt_def_typed" "make_init_opt_def";
val _ = emit "propagate_these_def_typed" "propagate_these_def";
val _ = emit "init_prop_def_typed" "init_prop_def";
val _ = emit "init_reduce_def_typed" "init_reduce_def";
val _ = emit "evaluate_init_code_typed" "evaluate_init_code";
val _ = emit "init_semantics_typed" "init_semantics";
val _ = emit "make_init_opt_SOME_semantics_typed" "make_init_opt_SOME_semantics";
val _ = emit "make_init_semantics_typed" "make_init_semantics";
val _ = emit "state_rel_inst_typed" "state_rel_inst";
val _ = emit "stack_remove_lab_pres_typed" "stack_remove_lab_pres";
val _ = emit "code_rel_loc_check_typed" "code_rel_loc_check";
val _ = emit "get_labels_comp_typed" "get_labels_comp";
val _ = emit "mem_val_def_typed" "mem_val_def";
val _ = emit "memory_def_typed" "memory_def";
val _ = emit "state_rel_mem_load_imp_typed" "state_rel_mem_load_imp";
val _ = emit "state_rel_mem_store_typed" "state_rel_mem_store";
val _ = emit "state_rel_mem_store_32_typed" "state_rel_mem_store_32";
val _ = emit "state_rel_mem_store_byte_aux_typed" "state_rel_mem_store_byte_aux";
val _ = emit "memory_fun2set_SUBSET_typed" "memory_fun2set_SUBSET";
val _ = emit "memory_write_typed" "memory_write";
val _ = emit "prog_comp_eta_typed" "prog_comp_eta";
val _ = emit "state_rel_const_typed" "state_rel_const";
val _ = emit "evaluate_single_stack_alloc_typed" "evaluate_single_stack_alloc";
val _ = emit "evaluate_stack_alloc_typed" "evaluate_stack_alloc";
val _ = emit "evaluate_single_stack_free_typed" "evaluate_single_stack_free";
val _ = emit "evaluate_stack_free_typed" "evaluate_stack_free";
val _ = emit "word_list_APPEND_typed" "word_list_APPEND";
val _ = emit "stack_heap_limit_ok_def_typed" "stack_heap_limit_ok_def";
val _ = emit "stack_write_typed" "stack_write";
val _ = emit "state_rel_stack_store_typed" "state_rel_stack_store";
val _ = emit "state_rel_get_var_k_typed" "state_rel_get_var_k";
val _ = emit "state_rel_def_typed" "state_rel_def";
val _ = emit "state_rel_set_var_typed" "state_rel_set_var";
val _ = emit "store_list_code_thm_typed" "store_list_code_thm";
val _ = emit "bytes_in_word_word_shift_typed" "bytes_in_word_word_shift";
val _ = emit "lsl_word_shift_typed" "lsl_word_shift";
val _ = emit "word_offset_eq_typed" "word_offset_eq";
val _ = emit "word_list_exists_thm_typed" "word_list_exists_thm";
val _ = emit "word_list_inj_typed" "word_list_inj";
val _ = emit "word_list_EL_in_memory_typed" "word_list_EL_in_memory";
val _ = emit "word_list_exists_ADD_typed" "word_list_exists_ADD";
val _ = emit "word_list_exists_addresses_typed" "word_list_exists_addresses";
val _ = emit "word_list_in_memory_typed" "word_list_in_memory";
val _ = emit "word_list_set_typed" "word_list_set";
val _ = emit "word_list_seteq_typed" "word_list_seteq";
val _ = emit "word_list_wrap_typed" "word_list_wrap";
val _ = emit "word_list_rev_def_typed" "word_list_rev_def";
val _ = emit "word_list_EQ_rev_typed" "word_list_EQ_rev";
val _ = emit "word_store_def_typed" "word_store_def";
