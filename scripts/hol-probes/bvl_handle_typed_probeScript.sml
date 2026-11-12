(* Typed source declarations for bvl_handle (task 148). *)
load "preamble";
load "bvl_handleTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvl_handleTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="bvl_handle",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by bvl_handle")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of bvl_handle")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "compile_def_typed" "compile_def";
val _ = emit "compile_sing_eq_typed" "compile_sing_eq";
val _ = emit "compile_exp_def_typed" "compile_exp_def";
val _ = emit "compile_exp_eq_typed" "compile_exp_eq";
val _ = emit "compile_seqs_def_typed" "compile_seqs_def";
val _ = emit "compile_any_def_typed" "compile_any_def";
val _ = emit "can_raise_def_typed" "can_raise_def";
val _ = emit "dest_handle_Raise_def_typed" "dest_handle_Raise_def";
val _ = emit "dest_handle_Let_def_typed" "dest_handle_Let_def";
val _ = emit "dest_handle_If_def_typed" "dest_handle_If_def";
val _ = emit "handle_adj_vars_def_typed" "handle_adj_vars_def";
val _ = emit "handle_size_def_typed" "handle_size_def";
val _ = emit "handle_simp_def_typed" "handle_simp_def";
val _ = emit "SmartLet_def_typed" "SmartLet_def";
val _ = emit "LetLet_def_typed" "LetLet_def";
val _ = emit "OptionalLetLet_sing_def_typed" "OptionalLetLet_sing_def";
val _ = emit "OptionalLetLet_def_typed" "OptionalLetLet_def";
val _ = emit "OptionalLetLet_sing_eq_typed" "OptionalLetLet_sing_eq";
val _ = emit "compile_sing_def_typed" "compile_sing_def";
