(* Typed source declarations for pan_to_crep (task 148). *)
load "preamble";
load "pan_to_crepTheory";
open HolKernel Parse boolLib bossLib;
open preamble pan_to_crepTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="pan_to_crep",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by pan_to_crep")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of pan_to_crep")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "cexp_heads_def_typed" "cexp_heads_def";
val _ = emit "comp_field_def_typed" "comp_field_def";
val _ = emit "compile_panop_def_typed" "compile_panop_def";
val _ = emit "ret_hdl_def_typed" "ret_hdl_def";
val _ = emit "ret_var_def_typed" "ret_var_def";
val _ = emit "wrap_rt_def_typed" "wrap_rt_def";
val _ = emit "crep_vars_def_typed" "crep_vars_def";
val _ = emit "comp_func_def_typed" "comp_func_def";
val _ = emit "compile_exp_def_typed" "compile_exp_def";
val _ = emit "compile_prog_def_typed" "compile_prog_def";
val _ = emit "compile_def_typed" "compile_def";
val _ = emit "compile_to_crep_def_typed" "compile_to_crep_def";
val _ = dt_label "context_typed" "context";
val _ = emit "get_eids_from_decls_def_typed" "get_eids_from_decls_def";
val _ = emit "make_funcs_def_typed" "make_funcs_def";
val _ = emit "mk_ctxt_def_typed" "mk_ctxt_def";
val _ = emit "exp_hdl_def_typed" "exp_hdl_def";
val _ = emit "make_vmap_def_typed" "make_vmap_def";
