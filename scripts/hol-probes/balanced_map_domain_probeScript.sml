load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib balanced_mapTheory;
val _ = Globals.linewidth := 10000;
val _ = if null (hyp to_fmap_key_set) then () else raise Fail "open HOL hypotheses";
val _ = (print "bmd_full_theorem="; print_thm to_fmap_key_set; print "\n");
