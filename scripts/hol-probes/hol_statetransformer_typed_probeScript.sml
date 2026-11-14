(* Typed HOL state_transformerTheory FOR_def at the pinned HOL revision. *)
load "bossLib";
load "state_transformerTheory";
open HolKernel Parse boolLib bossLib state_transformerTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "for_def_typed" state_transformerTheory.FOR_def;
