(* Typed HOL rich_listTheory statements at the pinned HOL revision:
   list_rel_lastn, LIST_REL_REPLICATE_same, SPLITP, SPLITL_def,
   SPLITP_NIL_FST_IMP and SPLITP_JOIN, printed with show_types. *)
load "bossLib";
load "rich_listTheory";
open HolKernel Parse boolLib bossLib rich_listTheory;
val _ = Globals.linewidth := 1000;
fun show_thm label th =
  (print label; print "=";
   Lib.with_flag (Globals.show_types, true) print_term (concl th);
   print "\n");
val _ = show_thm "list_rel_lastn_typed" rich_listTheory.list_rel_lastn;
val _ = show_thm "list_rel_replicate_same_typed" rich_listTheory.LIST_REL_REPLICATE_same;
val _ = show_thm "splitp_typed" rich_listTheory.SPLITP;
val _ = show_thm "splitl_def_typed" rich_listTheory.SPLITL_def;
val _ = show_thm "splitp_nil_fst_imp_typed" rich_listTheory.SPLITP_NIL_FST_IMP;
val _ = show_thm "splitp_join_typed" rich_listTheory.SPLITP_JOIN;
