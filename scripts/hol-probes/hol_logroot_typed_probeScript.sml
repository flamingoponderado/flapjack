(* Typed HOL logrootTheory statements at the pinned HOL revision: LOG_exists,
   the type of the new_specification constant LOG, the specification theorem
   LOG and LOG_UNIQUE, printed with show_types. *)
load "bossLib";
load "logrootTheory";
open HolKernel Parse boolLib bossLib logrootTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
fun show_type label c =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_type (type_of c);
   print "\n");
val _ = show_thm "log_exists_typed" logrootTheory.LOG_exists;
val _ = show_type "log_type" ``logroot$LOG``;
val _ = show_thm "log_spec_typed" logrootTheory.LOG;
val _ = show_thm "log_unique_typed" logrootTheory.LOG_UNIQUE;
