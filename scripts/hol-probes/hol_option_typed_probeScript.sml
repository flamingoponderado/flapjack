(* Typed HOL optionTheory statements at the pinned HOL revision: some_def,
   THE_DEF and OPTREL_def, printed with show_types. *)
load "bossLib";
load "optionTheory";
open HolKernel Parse boolLib bossLib optionTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "some_def_typed" optionTheory.some_def;
val _ = show_thm "the_def_typed" optionTheory.THE_DEF;
val _ = show_thm "optrel_def_typed" optionTheory.OPTREL_def;
