(* Typed source declarations for stack_namesProof (task 148). *)
load "preamble";
load "stack_namesProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble stack_namesProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="stack_namesProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by stack_namesProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of stack_namesProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "stack_names_stack_asm_ok_typed" "stack_names_stack_asm_ok";
val _ = emit "MAP_FST_compile_typed" "MAP_FST_compile";
val _ = emit "compile_semantics_typed" "compile_semantics";
val _ = emit "stack_names_call_args_typed" "stack_names_call_args";
val _ = emit "stack_names_lab_pres_typed" "stack_names_lab_pres";
val _ = emit "make_init_def_typed" "make_init_def";
val _ = emit "make_init_semantics_typed" "make_init_semantics";
val _ = emit "dec_clock_rename_state_typed" "dec_clock_rename_state";
val _ = emit "domain_rename_state_code_typed" "domain_rename_state_code";
val _ = emit "find_code_rename_state_typed" "find_code_rename_state";
val _ = emit "get_var_imm_find_name_typed" "get_var_imm_find_name";
val _ = emit "get_var_find_name_typed" "get_var_find_name";
val _ = emit "inst_rename_typed" "inst_rename";
val _ = emit "FLOOKUP_rename_state_find_name_typed" "FLOOKUP_rename_state_find_name";
val _ = emit "mem_load_rename_state_typed" "mem_load_rename_state";
val _ = emit "mem_store_rename_state_typed" "mem_store_rename_state";
val _ = emit "rename_state_def_typed" "rename_state_def";
val _ = emit "rename_state_const_typed" "rename_state_const";
val _ = emit "rename_state_with_clock_typed" "rename_state_with_clock";
val _ = emit "rename_state_with_memory_typed" "rename_state_with_memory";
val _ = emit "set_fp_var_find_name_typed" "set_fp_var_find_name";
val _ = emit "set_var_find_name_typed" "set_var_find_name";
val _ = emit "sh_mem_load16_rename_state_typed" "sh_mem_load16_rename_state";
val _ = emit "sh_mem_load32_rename_state_typed" "sh_mem_load32_rename_state";
val _ = emit "sh_mem_load_byte_rename_state_typed" "sh_mem_load_byte_rename_state";
val _ = emit "sh_mem_load_rename_state_typed" "sh_mem_load_rename_state";
val _ = emit "sh_mem_op_rename_store_typed" "sh_mem_op_rename_store";
val _ = emit "sh_mem_store16_rename_state_typed" "sh_mem_store16_rename_state";
val _ = emit "sh_mem_store32_rename_state_typed" "sh_mem_store32_rename_state";
val _ = emit "sh_mem_store_byte_rename_state_typed" "sh_mem_store_byte_rename_state";
val _ = emit "sh_mem_store_rename_state_typed" "sh_mem_store_rename_state";
