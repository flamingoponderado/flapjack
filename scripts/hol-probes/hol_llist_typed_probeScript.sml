(* Typed statements of the HOL `llist` theory declarations ported in
   `Flapjack/Misc/LList.lean`, from the built HOL4 core theory (no rebuild). *)
load "llistTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "fromList_11_typed=" llistTheory.fromList_11;
val _ = show_thm "LAPPEND_ASSOC_typed=" llistTheory.LAPPEND_ASSOC;
val _ = show_thm "LAPPEND_EQ_LNIL_typed=" llistTheory.LAPPEND_EQ_LNIL;
val _ = show_thm "LAPPEND_fromList_typed=" llistTheory.LAPPEND_fromList;
val _ = show_thm "LAPPEND11_FINITE1_typed=" llistTheory.LAPPEND11_FINITE1;
val _ = show_thm "LAPPEND_NIL_2ND_typed=" llistTheory.LAPPEND_NIL_2ND;
val _ = show_thm "LAPPEND_typed=" llistTheory.LAPPEND;
val _ = show_thm "LDROP_typed=" llistTheory.LDROP;
val _ = show_thm "LFINITE_fromList_typed=" llistTheory.LFINITE_fromList;
val _ = show_thm "LFINITE_APPEND_typed=" llistTheory.LFINITE_APPEND;
val _ = show_thm "LFINITE_LAPPEND_IMP_NIL_typed=" llistTheory.LFINITE_LAPPEND_IMP_NIL;
val _ = show_thm "NOT_LFINITE_APPEND_typed=" llistTheory.NOT_LFINITE_APPEND;
val _ = show_thm "LFLATTEN_typed=" llistTheory.LFLATTEN;
val _ = show_thm "LFLATTEN_EQ_NIL_typed=" llistTheory.LFLATTEN_EQ_NIL;
val _ = show_thm "LFLATTEN_THM_typed=" llistTheory.LFLATTEN_THM;
val _ = show_thm "every_def_typed=" llistTheory.every_def;
val _ = show_thm "every_thm_typed=" llistTheory.every_thm;
val _ = show_thm "exists_LNTH_typed=" llistTheory.exists_LNTH;
val _ = show_thm "LPREFIX_APPEND_typed=" llistTheory.LPREFIX_APPEND;
val _ = show_thm "to_fromList_typed=" llistTheory.to_fromList;
val _ = show_thm "LPREFIX_NTH_typed=" llistTheory.LPREFIX_NTH;
val _ = show_thm "LPREFIX_ANTISYM_typed=" llistTheory.LPREFIX_ANTISYM;
val _ = show_thm "LPREFIX_TRANS_typed=" llistTheory.LPREFIX_TRANS;
val _ = show_thm "prefixes_lprefix_total_typed=" llistTheory.prefixes_lprefix_total;
val _ = show_thm "from_toList_typed=" llistTheory.from_toList;
val _ = show_thm "LUNFOLD_def_typed=" llistTheory.LUNFOLD_def;
val _ = show_thm "LUNFOLD_typed=" llistTheory.LUNFOLD;
val _ = show_thm "LUNFOLD_UNIQUE_typed=" llistTheory.LUNFOLD_UNIQUE;
val _ = show_thm "LUNFOLD_BISIMULATION_typed=" llistTheory.LUNFOLD_BISIMULATION;
val _ = show_thm "LLIST_BISIMULATION0_typed=" llistTheory.LLIST_BISIMULATION0;
val _ = show_thm "LLIST_STRONG_BISIMULATION_typed=" llistTheory.LLIST_STRONG_BISIMULATION;
val _ = show_thm "every_coind_typed=" llistTheory.every_coind;
