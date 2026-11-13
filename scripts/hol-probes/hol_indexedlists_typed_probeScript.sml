(* Typed HOL indexedListsTheory findi_def at the pinned HOL revision. *)
load "bossLib";
load "indexedListsTheory";
open HolKernel Parse boolLib bossLib indexedListsTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "findi_def_typed" indexedListsTheory.findi_def;
