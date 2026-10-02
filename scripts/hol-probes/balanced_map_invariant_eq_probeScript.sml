load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib balanced_mapTheory pred_setTheory Tactical;
val _ = Globals.linewidth := 10000;
val _ = if null(hyp invariant_eq) then () else raise Fail "open HOL hypotheses";
val _ = (print "bmi_full="; print_thm invariant_eq; print "\n");
val _ = (print "bmi_typed="; Globals.show_types := true; print_thm invariant_eq; print "\n"; Globals.show_types := false);
val key_ordered_to_fmap = Tactical.prove (``!cmp k t res. good_cmp cmp ==> (key_ordered cmp k t res <=> !ks. ks IN FDOM (to_fmap cmp t) ==> key_set_cmp cmp k ks res)``, Tactical.THEN (Induct_on `t`, Tactical.THEN (rw [key_ordered_def,to_fmap_def], Tactical.THEN (Tactic.EQ_TAC, Tactical.THEN (rw [], metis_tac [key_set_cmp_thm])))));
val replay = prove(concl invariant_eq,
  rw [invariant_def] >> Tactic.EQ_TAC >> rw [DISJOINT_DEF, EXTENSION] >>
  Tactic.CCONTR_TAC >> fs [] >> Tactic.IMP_RES_TAC key_ordered_to_fmap >>
  Tactic.IMP_RES_TAC to_fmap_key_set >> gvs [key_set_cmp_thm] >>
  metis_tac [comparisonTheory.cmp_thms]);
val _ = if null(hyp replay) then () else raise Fail "open replay hypotheses";
val _ = (print "bmi_replay="; print_thm replay; print "\n");
val _ = (print "bmi_singleton="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 1 4 99 Tip Tip)``))); print "\n");
val _ = (print "bmi_badsize="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 0 4 99 Tip Tip)``))); print "\n");
val _ = (print "bmi_equal_child="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 2 4 99 (Bin 1 4 7 Tip Tip) Tip)``))); print "\n");
