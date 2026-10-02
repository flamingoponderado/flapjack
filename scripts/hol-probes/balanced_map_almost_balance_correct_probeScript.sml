load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse Tactic Rewrite simpLib bossLib Tactical BasicProvers arithmeticTheory comparisonTheory pred_setTheory finite_mapTheory balanced_mapTheory;
val _ = Globals.linewidth := 10000;
val TIMES_MIN = prove (``!x y z. x * MIN y z = MIN (x * y) (x * z)``, rw [MIN_DEF] >> fs []);
val almost_balancedL_thm = prove (``!l r.
    balanced l r
   ⇒
    almost_balancedL l r ∧ almost_balancedL (l + 1) r ∧
    almost_balancedL l (r - 1)``,
rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def] >>
 rw [MIN_DEF]);
val _ = if null(hyp almost_balancedL_thm) then () else raise Fail "open arithmetic theorem";
val _ = (print "almost_balancedL_thm="; Globals.show_types := true; print_thm almost_balancedL_thm; print "\n");
val almost_balancedR_thm = prove (``!l r.
    balanced l r
   ⇒
    almost_balancedR l r ∧ almost_balancedR l (r + 1) ∧
    almost_balancedR (l - 1) r``,
rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def] >>
 rw [MIN_DEF]);
val _ = if null(hyp almost_balancedR_thm) then () else raise Fail "open arithmetic theorem";
val _ = (print "almost_balancedR_thm="; Globals.show_types := true; print_thm almost_balancedR_thm; print "\n");
val _ = (print "bmac_L_0_0="; print_term(rand(concl(EVAL ``balanced 0 0 /\ almost_balancedL 0 0 /\ almost_balancedL (0+1) 0 /\ almost_balancedL 0 (0-1)``))); print "\n");
val _ = (print "bmac_R_0_0="; print_term(rand(concl(EVAL ``balanced 0 0 /\ almost_balancedR 0 0 /\ almost_balancedR 0 (0+1) /\ almost_balancedR (0-1) 0``))); print "\n");
val _ = (print "bmac_L_0_1="; print_term(rand(concl(EVAL ``balanced 0 1 /\ almost_balancedL 0 1 /\ almost_balancedL (0+1) 1 /\ almost_balancedL 0 (1-1)``))); print "\n");
val _ = (print "bmac_R_0_1="; print_term(rand(concl(EVAL ``balanced 0 1 /\ almost_balancedR 0 1 /\ almost_balancedR 0 (1+1) /\ almost_balancedR (0-1) 1``))); print "\n");
val _ = (print "bmac_L_1_0="; print_term(rand(concl(EVAL ``balanced 1 0 /\ almost_balancedL 1 0 /\ almost_balancedL (1+1) 0 /\ almost_balancedL 1 (0-1)``))); print "\n");
val _ = (print "bmac_R_1_0="; print_term(rand(concl(EVAL ``balanced 1 0 /\ almost_balancedR 1 0 /\ almost_balancedR 1 (0+1) /\ almost_balancedR (1-1) 0``))); print "\n");
val _ = (print "bmac_L_1_1="; print_term(rand(concl(EVAL ``balanced 1 1 /\ almost_balancedL 1 1 /\ almost_balancedL (1+1) 1 /\ almost_balancedL 1 (1-1)``))); print "\n");
val _ = (print "bmac_R_1_1="; print_term(rand(concl(EVAL ``balanced 1 1 /\ almost_balancedR 1 1 /\ almost_balancedR 1 (1+1) /\ almost_balancedR (1-1) 1``))); print "\n");
val _ = (print "bmac_L_1_3="; print_term(rand(concl(EVAL ``balanced 1 3 /\ almost_balancedL 1 3 /\ almost_balancedL (1+1) 3 /\ almost_balancedL 1 (3-1)``))); print "\n");
val _ = (print "bmac_R_1_3="; print_term(rand(concl(EVAL ``balanced 1 3 /\ almost_balancedR 1 3 /\ almost_balancedR 1 (3+1) /\ almost_balancedR (1-1) 3``))); print "\n");
val _ = (print "bmac_L_3_1="; print_term(rand(concl(EVAL ``balanced 3 1 /\ almost_balancedL 3 1 /\ almost_balancedL (3+1) 1 /\ almost_balancedL 3 (1-1)``))); print "\n");
val _ = (print "bmac_R_3_1="; print_term(rand(concl(EVAL ``balanced 3 1 /\ almost_balancedR 3 1 /\ almost_balancedR 3 (1+1) /\ almost_balancedR (3-1) 1``))); print "\n");
val _ = (print "bmac_L_2_6="; print_term(rand(concl(EVAL ``balanced 2 6 /\ almost_balancedL 2 6 /\ almost_balancedL (2+1) 6 /\ almost_balancedL 2 (6-1)``))); print "\n");
val _ = (print "bmac_R_2_6="; print_term(rand(concl(EVAL ``balanced 2 6 /\ almost_balancedR 2 6 /\ almost_balancedR 2 (6+1) /\ almost_balancedR (2-1) 6``))); print "\n");
val _ = (print "bmac_L_6_2="; print_term(rand(concl(EVAL ``balanced 6 2 /\ almost_balancedL 6 2 /\ almost_balancedL (6+1) 2 /\ almost_balancedL 6 (2-1)``))); print "\n");
val _ = (print "bmac_R_6_2="; print_term(rand(concl(EVAL ``balanced 6 2 /\ almost_balancedR 6 2 /\ almost_balancedR 6 (2+1) /\ almost_balancedR (6-1) 2``))); print "\n");
val _ = (print "bmac_L_3_9="; print_term(rand(concl(EVAL ``balanced 3 9 /\ almost_balancedL 3 9 /\ almost_balancedL (3+1) 9 /\ almost_balancedL 3 (9-1)``))); print "\n");
val _ = (print "bmac_R_3_9="; print_term(rand(concl(EVAL ``balanced 3 9 /\ almost_balancedR 3 9 /\ almost_balancedR 3 (9+1) /\ almost_balancedR (3-1) 9``))); print "\n");
val _ = (print "bmac_L_9_3="; print_term(rand(concl(EVAL ``balanced 9 3 /\ almost_balancedL 9 3 /\ almost_balancedL (9+1) 3 /\ almost_balancedL 9 (3-1)``))); print "\n");
val _ = (print "bmac_R_9_3="; print_term(rand(concl(EVAL ``balanced 9 3 /\ almost_balancedR 9 3 /\ almost_balancedR 9 (3+1) /\ almost_balancedR (9-1) 3``))); print "\n");
val _ = (print "bmac_L_10_30="; print_term(rand(concl(EVAL ``balanced 10 30 /\ almost_balancedL 10 30 /\ almost_balancedL (10+1) 30 /\ almost_balancedL 10 (30-1)``))); print "\n");
val _ = (print "bmac_R_10_30="; print_term(rand(concl(EVAL ``balanced 10 30 /\ almost_balancedR 10 30 /\ almost_balancedR 10 (30+1) /\ almost_balancedR (10-1) 30``))); print "\n");
val _ = (print "bmac_L_30_10="; print_term(rand(concl(EVAL ``balanced 30 10 /\ almost_balancedL 30 10 /\ almost_balancedL (30+1) 10 /\ almost_balancedL 30 (10-1)``))); print "\n");
val _ = (print "bmac_R_30_10="; print_term(rand(concl(EVAL ``balanced 30 10 /\ almost_balancedR 30 10 /\ almost_balancedR 30 (10+1) /\ almost_balancedR (30-1) 10``))); print "\n");
