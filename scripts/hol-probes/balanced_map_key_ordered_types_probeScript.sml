load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib balanced_mapTheory;
val _ = Globals.show_types := true;
val _ = Globals.linewidth := 10000;
val _ = (print "bmkt_ordered="; print_thm key_ordered_def; print "\n");
val _ = (print "bmkt_invariant="; print_thm invariant_def; print "\n");
val _ = if null(hyp key_ordered_def) andalso null(hyp invariant_def) then () else raise Fail "open hypotheses";
