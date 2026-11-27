(* Typed HOL WhileTheory statements at the pinned HOL revision: OLEAST_def,
   OLEAST_INTRO, OLEAST_EQ_SOME and OLEAST_EQ_NONE, printed with show_types. *)
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
val _ = show_thm "oleast_eq_some_typed" WhileTheory.OLEAST_EQ_SOME;
val _ = show_thm "oleast_eq_none_typed" WhileTheory.OLEAST_EQ_NONE;
