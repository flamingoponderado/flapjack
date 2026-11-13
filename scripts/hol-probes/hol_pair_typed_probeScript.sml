(* Typed HOL pairTheory statements at the pinned HOL revision: RPROD_DEF and
   LEX_DEF, printed with show_types. *)
load "bossLib";
load "pairTheory";
open HolKernel Parse boolLib bossLib pairTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "rprod_def_typed" pairTheory.RPROD_DEF;
val _ = show_thm "lex_def_typed" pairTheory.LEX_DEF;
