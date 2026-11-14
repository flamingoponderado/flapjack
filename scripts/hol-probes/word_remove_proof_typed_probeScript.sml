(* Typed source declarations for word_removeProof (task 148). *)
load "preamble";
load "word_removeProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble word_removeProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="word_removeProof",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by word_removeProof")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of word_removeProof")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "alloc_compile_state_typed" "alloc_compile_state";
val _ = emit "assign_compile_state_typed" "assign_compile_state";
val _ = emit "call_env_compile_state_typed" "call_env_compile_state";
val _ = emit "compile_state_def_typed" "compile_state_def";
val _ = emit "compile_state_const_typed" "compile_state_const";
val _ = emit "compile_state_dec_clock_typed" "compile_state_dec_clock";
val _ = emit "compile_state_update_typed" "compile_state_update";
val _ = emit "cut_state_compile_state_typed" "cut_state_compile_state";
val _ = emit "find_code_map_I_typed" "find_code_map_I";
val _ = emit "flush_state_compile_state_typed" "flush_state_compile_state";
val _ = emit "gc_compile_state_typed" "gc_compile_state";
val _ = emit "get_fp_var_compile_state_typed" "get_fp_var_compile_state";
val _ = emit "get_store_compile_state_typed" "get_store_compile_state";
val _ = emit "get_var_imm_compile_state_typed" "get_var_imm_compile_state";
val _ = emit "get_var_compile_state_typed" "get_var_compile_state";
val _ = emit "get_vars_compile_state_typed" "get_vars_compile_state";
val _ = emit "has_space_compile_state_typed" "has_space_compile_state";
val _ = emit "inst_compile_state_typed" "inst_compile_state";
val _ = emit "jump_exc_compile_state_typed" "jump_exc_compile_state";
val _ = emit "mem_load_compile_state_typed" "mem_load_compile_state";
val _ = emit "mem_store_compile_state_typed" "mem_store_compile_state";
val _ = emit "pop_env_compile_state_typed" "pop_env_compile_state";
val _ = emit "push_env_case_handler_typed" "push_env_case_handler";
val _ = emit "push_env_compile_state_typed" "push_env_compile_state";
val _ = emit "set_fp_var_compile_state_typed" "set_fp_var_compile_state";
val _ = emit "set_store_compile_state_typed" "set_store_compile_state";
val _ = emit "set_var_compile_state_typed" "set_var_compile_state";
val _ = emit "set_vars_compile_state_typed" "set_vars_compile_state";
val _ = emit "unset_var_compile_state_typed" "unset_var_compile_state";
val _ = emit "word_exp_compile_state_typed" "word_exp_compile_state";
val _ = emit "word_remove_correct_typed" "word_remove_correct";
