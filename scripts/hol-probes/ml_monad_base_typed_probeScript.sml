(* Typed source declarations for ml_monadBase (task 148). *)
load "preamble";
load "ml_monadBaseTheory";
open HolKernel Parse boolLib bossLib;
open preamble ml_monadBaseTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="ml_monadBase",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by ml_monadBase")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of ml_monadBase")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "exc_typed" "exc";
val _ = emit "Marray_alloc_def_typed" "Marray_alloc_def";
val _ = emit "st_ex_bind_def_typed" "st_ex_bind_def";
val _ = emit "st_ex_ignore_bind_def_typed" "st_ex_ignore_bind_def";
val _ = emit "st_ex_return_def_typed" "st_ex_return_def";
val _ = emit "run_def_typed" "run_def";
val _ = emit "Marray_length_def_typed" "Marray_length_def";
val _ = emit "Marray_sub_def_typed" "Marray_sub_def";
val _ = emit "Marray_update_def_typed" "Marray_update_def";
val _ = emit "Msub_eq_typed" "Msub_eq";
val _ = emit "Mupdate_eq_typed" "Mupdate_eq";
val _ = emit "Msub_def_typed" "Msub_def";
val _ = emit "Msub_exn_eq_typed" "Msub_exn_eq";
val _ = emit "Mupdate_def_typed" "Mupdate_def";
val _ = emit "Mupdate_exn_eq_typed" "Mupdate_exn_eq";
