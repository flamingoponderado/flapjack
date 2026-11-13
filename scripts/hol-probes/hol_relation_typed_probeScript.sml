(* Typed HOL relationTheory statements at the pinned HOL revision:
   transitive_def and total_def, printed with show_types. *)
load "bossLib";
load "relationTheory";
open HolKernel Parse boolLib bossLib relationTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "transitive_def_typed" relationTheory.transitive_def;
val _ = show_thm "total_def_typed" relationTheory.total_def;
