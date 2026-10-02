load "bossLib";
load "comparisonTheory";
open HolKernel Parse bossLib comparisonTheory;
val _ = Globals.linewidth := 10000;
val _ = if null(hyp cmp_thms) then () else raise Fail "open HOL hypotheses";
val _ = (print "cmp_full_bundle="; print_thm cmp_thms; print "\n");
val _ = (print "cmp_full_typed="; Globals.show_types := true; print_thm cmp_thms; print "\n"; Globals.show_types := false);
