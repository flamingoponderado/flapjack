(* Typed HOL WhileTheory statements at the pinned HOL revision: OLEAST_def and
   OLEAST_INTRO, printed with show_types. *)
load "bossLib";
load "WhileTheory";
open HolKernel Parse boolLib bossLib WhileTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "oleast_def_typed" WhileTheory.OLEAST_def;
val _ = show_thm "oleast_intro_typed" WhileTheory.OLEAST_INTRO;
