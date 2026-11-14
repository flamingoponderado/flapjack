(* Typed source declarations for infer_t (task 148). *)
load "preamble";
load "infer_tTheory";
open HolKernel Parse boolLib bossLib;
open preamble infer_tTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun fetch1 name = DB.lookup {Thy="infer_t",Name=name};

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case fetch1 name of
    NONE => raise Fail (label ^ " is not exported by infer_t")
  | SOME (th,_) => show label th;

fun dt_label label name =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first [0,1,2,3,4] of
      NONE => raise Fail (label ^ " is not a datatype of infer_t")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

val _ = dt_label "infer_t_typed" "infer_t";
val _ = emit "get_tyname_def_typed" "get_tyname_def";
val _ = emit "type_ident_to_string_def_typed" "type_ident_to_string_def";
val _ = emit "ty_var_name_def_typed" "ty_var_name_def";
val _ = emit "add_parens_def_typed" "add_parens_def";
val _ = emit "inf_type_to_string_rec_def_typed" "inf_type_to_string_rec_def";
val _ = emit "inf_type_to_string_def_typed" "inf_type_to_string_def";
