(* Typed HOL bitTheory LOG2_def at the pinned HOL revision. *)
load "bossLib";
load "bitTheory";
open HolKernel Parse boolLib bossLib bitTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "log2_def_typed" bitTheory.LOG2_def;
