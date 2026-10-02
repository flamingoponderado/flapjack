load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib balanced_mapTheory;
val _ = Globals.show_types := true;
val _ = Globals.linewidth := 10000;
val _ = (print "bmct_lookup="; print_thm lookup_def; print "\n");
val _ = (print "bmct_member="; print_thm member_def; print "\n");
val _ = if null(hyp lookup_def) andalso null(hyp member_def) then () else raise Fail "open core hypotheses";
