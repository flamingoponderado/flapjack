load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib balanced_mapTheory;
val _ = Globals.linewidth := 10000;
val _ = if null(hyp null_thm) then () else raise Fail "open HOL hypotheses";
val _ = (print "bmn_full="; print_thm null_thm; print "\n");
val _ = (print "bmn_typed="; Globals.show_types := true; print_thm null_thm; print "\n"; Globals.show_types := false);
val _ = (print "bmn_tip="; print_term(rand(concl(EVAL ``null (Tip:(num,num)balanced_map)``))); print "\n");
val _ = (print "bmn_bin_badsize="; print_term(rand(concl(EVAL ``null (Bin 0 1 99 Tip Tip)``))); print "\n");
