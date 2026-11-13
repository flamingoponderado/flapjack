(* Typed HOL totoTheory TotOrd definition at the pinned HOL revision. *)
load "bossLib";
load "totoTheory";
open HolKernel Parse boolLib bossLib totoTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "totord_typed" totoTheory.TotOrd;
