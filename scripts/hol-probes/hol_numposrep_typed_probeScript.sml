(* Typed HOL numposrepTheory n2l_def at the pinned HOL revision. *)
load "bossLib";
load "numposrepTheory";
open HolKernel Parse boolLib bossLib numposrepTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "n2l_def_typed" numposrepTheory.n2l_def;
