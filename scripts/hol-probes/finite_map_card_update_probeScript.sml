load "bossLib";
load "finite_mapTheory";
open HolKernel Parse Tactical bossLib finite_mapTheory;
val _ = Globals.linewidth := 10000;
val replay = prove (``!fm a b. FCARD (FUPDATE fm (a,b)) =
    if a IN FDOM fm then FCARD fm else 1 + FCARD fm``,
  SRW_TAC [numSimps.ARITH_ss][FCARD_DEF, FDOM_FUPDATE, FDOM_FINITE]);
val _ = if null(hyp replay) then () else raise Fail "open FCARD_FUPDATE";
val _ = (print "FCARD_FUPDATE="; Globals.show_types := true; print_thm replay; print "\n");
val _ = (print "fmcard_empty="; print_term(rand(concl(SIMP_CONV (srw_ss()) [FCARD_FUPDATE, FCARD_FEMPTY, FDOM_FUPDATE, FDOM_FEMPTY] ``FCARD ((FEMPTY:num |-> num) |+ (1,10))``))); print "\n");
val _ = (print "fmcard_replace="; print_term(rand(concl(SIMP_CONV (srw_ss()) [FCARD_FUPDATE, FCARD_FEMPTY, FDOM_FUPDATE, FDOM_FEMPTY] ``FCARD ((FEMPTY:num |-> num) |+ (1,10) |+ (1,20))``))); print "\n");
val _ = (print "fmcard_fresh="; print_term(rand(concl(SIMP_CONV (srw_ss()) [FCARD_FUPDATE, FCARD_FEMPTY, FDOM_FUPDATE, FDOM_FEMPTY] ``FCARD ((FEMPTY:num |-> num) |+ (1,10) |+ (2,30))``))); print "\n");
val _ = (print "fmcard_repeat="; print_term(rand(concl(SIMP_CONV (srw_ss()) [FCARD_FUPDATE, FCARD_FEMPTY, FDOM_FUPDATE, FDOM_FEMPTY] ``FCARD ((FEMPTY:num |-> num) |+ (1,10) |+ (1,20) |+ (1,40))``))); print "\n");
