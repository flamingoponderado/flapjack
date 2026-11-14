(* Typed HOL pred_setTheory statements at the pinned HOL revision: INJ_DEF,
   LINV_LO and LINV_OPT_def, printed with show_types. *)
load "bossLib";
load "pred_setTheory";
open HolKernel Parse boolLib bossLib pred_setTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "inj_def_typed" pred_setTheory.INJ_DEF;
val _ = show_thm "linv_lo_typed" pred_setTheory.LINV_LO;
val _ = show_thm "linv_opt_def_typed" pred_setTheory.LINV_OPT_def;
