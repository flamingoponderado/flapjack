(* Typed source declarations for panLang (task 148). *)
load "preamble";
load "panLangTheory";
open HolKernel Parse boolLib bossLib;
open preamble panLangTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="panLang",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by panLang")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of panLang")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "opsize_typed" "opsize";
val _ = dt_label "shift_typed" "shift";
val _ = dt_label "panop_typed" "panop";
val _ = dt_label "primop_typed" "primop";
val _ = dt_label "varkind_typed" "varkind";
val _ = dt_label "decl_typed" "decl";
val _ = dt_label "fun_decl_typed" "fun_decl";
val _ = dt_label "struct_info_typed" "struct_info";
val _ = emit "exceptions_def_typed" "exceptions_def";
val _ = emit "functions_def_typed" "functions_def";
val _ = emit "inlinable_def_typed" "inlinable_def";
val _ = emit "is_decl_def_typed" "is_decl_def";
val _ = emit "is_exn_decl_def_typed" "is_exn_decl_def";
val _ = emit "is_function_def_typed" "is_function_def";
val _ = emit "is_name_def_typed" "is_name_def";
val _ = emit "is_wf_ctxt_def_typed" "is_wf_ctxt_def";
val _ = emit "is_wf_flds_def_typed" "is_wf_flds_def";
val _ = emit "is_wf_shape_def_typed" "is_wf_shape_def";
val _ = emit "size_of_eids_def_typed" "size_of_eids_def";
val _ = emit "size_of_sh_with_ctxt_def_typed" "size_of_sh_with_ctxt_def";
val _ = dt_label "exp_typed" "exp";
val _ = emit "global_var_exp_def_typed" "global_var_exp_def";
val _ = emit "MEM_IMP_exp_size_typed" "MEM_IMP_exp_size";
val _ = emit "shape_val_def_typed" "shape_val_def";
val _ = emit "var_exp_def_typed" "var_exp_def";
val _ = dt_label "prog_typed" "prog";
val _ = emit "exp_ids_def_typed" "exp_ids_def";
val _ = emit "free_var_ids_def_typed" "free_var_ids_def";
val _ = emit "fun_ids_def_typed" "fun_ids_def";
val _ = emit "nested_seq_def_typed" "nested_seq_def";
val _ = dt_label "shape_typed" "shape";
val _ = emit "MEM_IMP_shape_size_typed" "MEM_IMP_shape_size";
val _ = emit "shape_to_str_def_typed" "shape_to_str_def";
val _ = emit "size_of_shape_def_typed" "size_of_shape_def";
val _ = emit "with_shape_def_typed" "with_shape_def";
val _ = emit "load_op_def_typed" "load_op_def";
val _ = emit "store_op_def_typed" "store_op_def";
