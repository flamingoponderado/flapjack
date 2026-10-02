load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib balanced_mapTheory;
val _ = Globals.linewidth := 10000;
val replay = Tactical.prove (``!cmp k t res. good_cmp cmp ==> (key_ordered cmp k t res <=> !ks. ks IN FDOM (to_fmap cmp t) ==> key_set_cmp cmp k ks res)``, Tactical.THEN (Induct_on `t`, Tactical.THEN (rw [key_ordered_def,to_fmap_def], Tactical.THEN (Tactic.EQ_TAC, Tactical.THEN (rw [], metis_tac [key_set_cmp_thm])))));
val _ = if null(hyp replay) then () else raise Fail "open HOL hypotheses";
val _ = (print "bmko_full_theorem="; print_thm replay; print "\n");
