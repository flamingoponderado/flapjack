(* Typed source declarations for panSem (task 148). *)
load "preamble";
load "panSemTheory";
open HolKernel Parse boolLib bossLib;
open preamble panSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="panSem",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by panSem")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of panSem")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "word_lab_typed" "word_lab";
val _ = emit "vshapes_args_rel_imp_eq_len_MAP_typed" "vshapes_args_rel_imp_eq_len_MAP";
val _ = dt_label "result_typed" "result";
val _ = emit "decs_stcnames_def_typed" "decs_stcnames_def";
val _ = emit "eval_ind_typed" "eval_ind";
val _ = emit "evaluate_def_typed" "evaluate_def";
val _ = emit "evaluate_clock_typed" "evaluate_clock";
val _ = emit "fix_clock_evaluate_typed" "fix_clock_evaluate";
val _ = emit "evaluate_ind_typed" "evaluate_ind";
val _ = emit "mem_load_32_alt_typed" "mem_load_32_alt";
val _ = emit "mem_load_def_typed" "mem_load_def";
val _ = emit "mem_store_32_alt_typed" "mem_store_32_alt";
val _ = emit "semantics_def_typed" "semantics_def";
val _ = emit "semantics_decls_def_typed" "semantics_decls_def";
val _ = dt_label "state_typed" "state";
val _ = emit "dec_clock_def_typed" "dec_clock_def";
val _ = emit "empty_locals_def_typed" "empty_locals_def";
val _ = emit "eval_def_typed" "eval_def";
val _ = emit "evaluate_decls_def_typed" "evaluate_decls_def";
val _ = emit "fix_clock_def_typed" "fix_clock_def";
val _ = emit "is_valid_value_def_typed" "is_valid_value_def";
val _ = emit "lookup_code_def_typed" "lookup_code_def";
val _ = emit "lookup_kvar_def_typed" "lookup_kvar_def";
val _ = emit "set_global_def_typed" "set_global_def";
val _ = emit "set_kvar_def_typed" "set_kvar_def";
val _ = emit "set_var_def_typed" "set_var_def";
val _ = emit "sh_mem_load_def_typed" "sh_mem_load_def";
val _ = dt_label "v_typed" "v";
val _ = emit "flatten_def_typed" "flatten_def";
val _ = emit "isValWord_def_typed" "isValWord_def";
val _ = emit "pan_primop_def_typed" "pan_primop_def";
val _ = emit "theValWord_def_typed" "theValWord_def";
val _ = emit "isWord_def_typed" "isWord_def";
val _ = emit "nb_op_def_typed" "nb_op_def";
val _ = emit "mem_load_32_def_typed" "mem_load_32_def";
val _ = emit "mem_load_byte_def_typed" "mem_load_byte_def";
val _ = emit "mem_store_32_def_typed" "mem_store_32_def";
val _ = emit "mem_store_byte_def_typed" "mem_store_byte_def";
val _ = emit "mem_store_def_typed" "mem_store_def";
val _ = emit "mem_stores_def_typed" "mem_stores_def";
val _ = emit "pan_op_def_typed" "pan_op_def";
val _ = emit "write_bytearray_def_typed" "write_bytearray_def";
val _ = emit "theWord_def_typed" "theWord_def";
val _ = emit "kvar_simps_typed" "kvar_simps";
val _ = emit "is_valid_value_simps_typed" "is_valid_value_simps";
val _ = emit "upd_locals_def_typed" "upd_locals_def";
val _ = emit "res_var_def_typed" "res_var_def";
val _ = emit "sh_mem_store_def_typed" "sh_mem_store_def";
