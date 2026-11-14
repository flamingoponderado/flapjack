(* Typed capture for tokenUtilsTheory destLf (task 160), the leaf destructor
   used by the CakeParser exact parsetree ports. *)
load "tokenUtilsTheory";
open HolKernel Parse boolLib bossLib tokenUtilsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "tokenUtils", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in tokenUtils>\n");

val _ = emit "destLf_def_typed" "destLf_def";
