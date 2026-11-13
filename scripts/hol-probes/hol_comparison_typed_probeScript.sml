(* Typed HOL comparisonTheory statements at the pinned HOL revision:
   good_cmp_def, TotOrder_imp_good_cmp and cmp_thms, printed with show_types. *)
load "bossLib";
load "comparisonTheory";
load "totoTheory";
open HolKernel Parse boolLib bossLib comparisonTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "good_cmp_def_typed" comparisonTheory.good_cmp_def;
val _ = show_thm "totorder_imp_good_cmp_typed" comparisonTheory.TotOrder_imp_good_cmp;
val _ = show_thm "cmp_thms_typed" comparisonTheory.cmp_thms;
