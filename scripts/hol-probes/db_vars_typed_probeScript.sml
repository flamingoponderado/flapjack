(* Typed source declarations for db_vars (task 148). *)
load "preamble";
load "db_varsTheory";
open HolKernel Parse boolLib bossLib;
open preamble db_varsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="db_vars",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by db_vars")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of db_vars")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = emit "has_var_mk_Union_typed" "has_var_mk_Union";
val _ = dt_label "db_var_set_typed" "db_var_set";
val _ = emit "mk_Union_def_typed" "mk_Union_def";
val _ = emit "list_mk_Union_def_typed" "list_mk_Union_def";
val _ = emit "db_to_set_acc_def_typed" "db_to_set_acc_def";
val _ = emit "db_to_set_def_typed" "db_to_set_def";
val _ = emit "vars_to_list_def_typed" "vars_to_list_def";
val _ = emit "vars_from_list_def_typed" "vars_from_list_def";
val _ = emit "vars_flatten_def_typed" "vars_flatten_def";
val _ = emit "has_var_def_typed" "has_var_def";
val _ = emit "has_var_vars_flatten_typed" "has_var_vars_flatten";
val _ = emit "lookup_db_to_set_typed" "lookup_db_to_set";
val _ = emit "lookup_db_to_set_acc_typed" "lookup_db_to_set_acc";
val _ = emit "MEM_vars_from_list_typed" "MEM_vars_from_list";
val _ = emit "MEM_vars_to_list_typed" "MEM_vars_to_list";
