(* Typed capture for crep_to_loopScript.sml `rt_vars_def` (task 159), the
   definition behind the Flapjack raw-function `rtVars` analogue. Exported with
   show_types from the loaded crep_to_loopTheory; the finite map type is HOL
   `num |-> num` (a `|->` finite map), and `OPT_MMAP (FLOOKUP fm) vs` is the
   polymorphic optional-map projection. *)
load "preamble";
load "crep_to_loopTheory";
open HolKernel Parse boolLib bossLib preamble crep_to_loopTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

fun emit label name =
  case DB.lookup {Thy = "crep_to_loop", Name = name} of
    SOME (th, _) => show label th
  | NONE => print (label ^ "=<not found in crep_to_loop>\n");

val _ = emit "rt_vars_def_typed" "rt_vars_def";
