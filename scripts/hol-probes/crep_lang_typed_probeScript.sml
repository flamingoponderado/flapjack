(* Typed source declarations for crepLang (task 148). *)
load "preamble";
load "crepLangTheory";
open HolKernel Parse boolLib bossLib;
open preamble crepLangTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="crepLang",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by crepLang")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of crepLang")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "assign_ret_def_typed" "assign_ret_def";
val _ = emit "assigned_free_vars_def_typed" "assigned_free_vars_def";
val _ = emit "assigned_vars_def_typed" "assigned_vars_def";
val _ = emit "var_cexp_def_typed" "var_cexp_def";
val _ = emit "exps_def_typed" "exps_def";
val _ = emit "nested_seq_def_typed" "nested_seq_def";
val _ = emit "load_globals_def_typed" "load_globals_def";
val _ = emit "nested_decs_def_typed" "nested_decs_def";
val _ = emit "store_globals_def_typed" "store_globals_def";
val _ = emit "stores_def_typed" "stores_def";
val _ = dt_label "exp_typed" "exp";
val _ = emit "load_shape_def_typed" "load_shape_def";
val _ = dt_label "prog_typed" "prog";
