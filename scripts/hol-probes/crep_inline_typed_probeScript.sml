(* Typed source declarations for crep_inline (task 148). *)
load "preamble";
load "crep_inlineTheory";
open HolKernel Parse boolLib bossLib;
open preamble crep_inlineTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="crep_inline",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by crep_inline")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of crep_inline")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "early_exit_typed" "early_exit";
val _ = emit "var_prog_def_typed" "var_prog_def";
val _ = emit "vmax_prog_def_typed" "vmax_prog_def";
val _ = emit "unreach_elim_def_typed" "unreach_elim_def";
val _ = emit "compile_inl_prog_def_typed" "compile_inl_prog_def";
val _ = emit "compile_inl_top_def_typed" "compile_inl_top_def";
val _ = emit "inline_prog_def_typed" "inline_prog_def";
val _ = emit "arg_load_def_typed" "arg_load_def";
val _ = emit "has_return_def_typed" "has_return_def";
val _ = emit "inline_nontail_def_typed" "inline_nontail_def";
val _ = emit "inline_tail_def_typed" "inline_tail_def";
val _ = emit "not_branch_ret_def_typed" "not_branch_ret_def";
val _ = emit "transform_branch_def_typed" "transform_branch_def";
val _ = emit "transform_eoc_def_typed" "transform_eoc_def";
