load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib balanced_mapTheory;
val _ = Globals.linewidth := 10000;
val replay = Tactical.prove (``!cmp t. invariant cmp t ==> size t = structure_size t``, Tactical.THEN (Cases_on `t`, rw [size_def,invariant_def,structure_size_def]));
val _ = if null(hyp replay) then () else raise Fail "open HOL hypotheses";
val _ = (print "bmss_full_theorem="; print_thm replay; print "\n");
