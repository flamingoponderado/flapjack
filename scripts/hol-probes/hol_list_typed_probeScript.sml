(* Typed HOL listTheory statements at the pinned HOL revision: HD, LAST_DEF,
   LAST_CONS, EL_def, EVERY2_LUPDATE_same, list_size_thm and oHD_def, printed
   with show_types so that every independently quantified type variable is
   visible. *)
load "bossLib";
load "listTheory";
open HolKernel Parse boolLib bossLib listTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "hd_typed" listTheory.HD;
val _ = show_thm "last_def_typed" listTheory.LAST_DEF;
val _ = show_thm "last_cons_typed" listTheory.LAST_CONS;
val _ = show_thm "el_def_typed" listTheory.EL_def;
val _ = show_thm "every2_lupdate_same_typed" listTheory.EVERY2_LUPDATE_same;
val _ = show_thm "list_size_thm_typed" listTheory.list_size_thm;
val _ = show_thm "ohd_def_typed" listTheory.oHD_def;
