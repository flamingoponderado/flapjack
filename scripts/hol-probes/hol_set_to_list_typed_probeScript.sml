(* Typed HOL pred_set CHOICE/REST and list SET_TO_LIST statements at the pinned
   HOL revision, printed with show_types (hypotheses first), for the Flapjack
   SET_TO_LIST rendering (Flapjack/Misc/PredSet.lean, Flapjack/Misc/List.lean). *)
load "bossLib";
load "listTheory";
open HolKernel Parse boolLib bossLib listTheory pred_setTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   app (fn h => (Lib.with_flag (Globals.show_types, true) print_term h; print " ==> ")) (hyp th);
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "choice_def_typed" pred_setTheory.CHOICE_DEF;
val _ = show_thm "rest_def_typed" pred_setTheory.REST_DEF;
val _ = show_thm "set_to_list_thm_typed" listTheory.SET_TO_LIST_THM;
val _ = show_thm "set_to_list_in_mem_typed" listTheory.SET_TO_LIST_IN_MEM;
val _ = show_thm "mem_set_to_list_typed" listTheory.MEM_SET_TO_LIST;
