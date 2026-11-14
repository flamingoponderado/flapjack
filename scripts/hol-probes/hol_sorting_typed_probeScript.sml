(* Typed HOL sortingTheory statements at the pinned HOL revision: PERM_DEF,
   SORTED_DEF, SORTED_EQ, SORTED_TL, PART_DEF, PARTs_HAVE_PROP and
   PARTITION_DEF, printed with show_types so that every independently
   quantified type variable is visible. *)
load "bossLib";
load "sortingTheory";
open HolKernel Parse boolLib bossLib sortingTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "perm_def_typed" sortingTheory.PERM_DEF;
val _ = show_thm "sorted_def_typed" sortingTheory.SORTED_DEF;
val _ = show_thm "sorted_eq_typed" sortingTheory.SORTED_EQ;
val _ = show_thm "sorted_tl_typed" sortingTheory.SORTED_TL;
val _ = show_thm "part_def_typed" sortingTheory.PART_DEF;
val _ = show_thm "parts_have_prop_typed" sortingTheory.PARTs_HAVE_PROP;
val _ = show_thm "partition_def_typed" sortingTheory.PARTITION_DEF;
