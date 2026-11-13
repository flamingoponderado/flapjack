(* Typed capture for the generic grammar carriers and destructors used by the
   CakeParser exact ports (task 160): the HOL `symbol` and `parsetree`
   datatypes with inferred constructor types, and the grammarScript destructor
   definitions ptree_loc/ptree_list_loc/ptree_head/isTOK/destTOK. *)
load "grammarTheory";
open HolKernel Parse boolLib bossLib grammarTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun dt label name arities =
  let
    fun try n =
      let val ty = mk_type (name, List.tabulate (n, fn _ => alpha))
      in SOME (TypeBase.constructors_of ty) end handle _ => NONE
    fun first [] = NONE | first (n::ns) = case try n of SOME c => SOME c | NONE => first ns
  in
    case first arities of
      NONE => raise Fail (label ^ " is not a datatype")
    | SOME cs => (print (label ^ "=");
        print (String.concatWith "; " (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end) cs));
        print "\n")
  end;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "grammar", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in grammar>\n");

val _ = dt "symbol_typed" "symbol" [2];
val _ = dt "parsetree_typed" "parsetree" [3];
val _ = emit "ptree_loc_def_typed" "ptree_loc_def";
val _ = emit "ptree_list_loc_def_typed" "ptree_list_loc_def";
val _ = emit "ptree_head_def_typed" "ptree_head_def";
val _ = emit "isTOK_def_typed" "isTOK_def";
val _ = emit "destTOK_def_typed" "destTOK_def";
