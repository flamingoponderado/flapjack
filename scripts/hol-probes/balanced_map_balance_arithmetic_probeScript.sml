load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib Tactical arithmeticTheory balanced_mapTheory;
val _ = Globals.linewidth := 10000;
val _ = Globals.show_types := true;
val rw = srw_tac [ARITH_ss];
fun fs x = full_simp_tac (srw_ss()++ARITH_ss) x;
val TIMES_MIN = prove (``!x y z. x * MIN y z = MIN (x * y) (x * z)``, rw [MIN_DEF] >> fs []);
val _ = (print "bma_left="; print_thm almost_balancedL_def; print "\n");
val _ = (print "bma_right="; print_thm almost_balancedR_def; print "\n");
val balanced_lem1 = prove (``!l r. l + r ≤ 1 ⇒ balanced l r``, rw [balanced_def]);
val _ = if null(hyp balanced_lem1) then () else raise Fail "open balanced_lem1";
val _ = (print "bma_lem1="; print_thm balanced_lem1; print "\n");
val balanced_lem2 = prove (``!l r.
    ¬(l > delta * r) ∧
    almost_balancedL l r ∧
    ¬(l + r ≤ 1)
  ⇒
    balanced l r``, rw [almost_balancedL_def, balanced_def, NOT_LESS_EQUAL, NOT_GREATER,
          TIMES_MIN, delta_def]);
val _ = if null(hyp balanced_lem2) then () else raise Fail "open balanced_lem2";
val _ = (print "bma_lem2="; print_thm balanced_lem2; print "\n");
val balanced_lem3 = prove (``!b b0 r.
     almost_balancedL (b + b0 + 1) r ∧
     b + b0 + 1 > delta * r ∧
     b0 < ratio * b ∧
     balanced b b0
   ⇒
     balanced b (b0 + r + 1) ∧
     balanced b0 r``, rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def, ratio_def]);
val _ = if null(hyp balanced_lem3) then () else raise Fail "open balanced_lem3";
val _ = (print "bma_lem3="; print_thm balanced_lem3; print "\n");
val balanced_lem4 = prove (``!b b' b0' r.
  almost_balancedL (b + b' + b0' + 2) r ∧
  b + b' + b0' + 2 > delta * r ∧
  ¬(b' + b0' + 1 < ratio * b) ∧
  balanced b (b' + b0' + 1) ∧
  balanced b' b0'
  ⇒
  balanced (b + b' + 1) (b0' + r + 1) ∧
  balanced b b' ∧
  balanced b0' r``, rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def, ratio_def]);
val _ = if null(hyp balanced_lem4) then () else raise Fail "open balanced_lem4";
val _ = (print "bma_lem4="; print_thm balanced_lem4; print "\n");
val balanced_lem5 = prove (``!l r.
   ¬(r > delta * l) ∧ almost_balancedR l r
  ⇒
   balanced l r``, rw [almost_balancedR_def, balanced_def, NOT_LESS_EQUAL, NOT_GREATER,
          TIMES_MIN, delta_def]);
val _ = if null(hyp balanced_lem5) then () else raise Fail "open balanced_lem5";
val _ = (print "bma_lem5="; print_thm balanced_lem5; print "\n");
val balanced_lem6 = prove (``!b b0 l.
    almost_balancedR l (b + b0 + 1) ∧
    b + b0 + 1 > delta * l ∧
    b < ratio * b0 ∧
    balanced b b0
   ⇒
    balanced (b + l + 1) b0 ∧ balanced l b``, rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def, ratio_def]);
val _ = if null(hyp balanced_lem6) then () else raise Fail "open balanced_lem6";
val _ = (print "bma_lem6="; print_thm balanced_lem6; print "\n");
val balanced_lem7 = prove (``!b b0 b0' l b'.
    almost_balancedR l (b' + b0 + b0' + 2) ∧
    b' + b0 + b0' + 2 > delta * l ∧
    ¬(b' + b0' + 1 < ratio * b0) ∧
    balanced (b' + b0' + 1) b0 ∧
    balanced b' b0'
   ⇒
    balanced (b' + l + 1) (b0 + b0' + 1) ∧
    balanced l b' ∧
    balanced b0' b0``, rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def, ratio_def]);
val _ = if null(hyp balanced_lem7) then () else raise Fail "open balanced_lem7";
val _ = (print "bma_lem7="; print_thm balanced_lem7; print "\n");
val _ = (print "bma_left00="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedL 0 0``))); print "\n");
val _ = (print "bma_left40="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedL 4 0``))); print "\n");
val _ = (print "bma_left50="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedL 5 0``))); print "\n");
val _ = (print "bma_left71="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedL 7 1``))); print "\n");
val _ = (print "bma_left81="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedL 8 1``))); print "\n");
val _ = (print "bma_left92="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedL 9 2``))); print "\n");
val _ = (print "bma_left102="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedL 10 2``))); print "\n");
val _ = (print "bma_right00="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedR 0 0``))); print "\n");
val _ = (print "bma_right04="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedR 0 4``))); print "\n");
val _ = (print "bma_right05="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedR 0 5``))); print "\n");
val _ = (print "bma_right17="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedR 1 7``))); print "\n");
val _ = (print "bma_right18="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedR 1 8``))); print "\n");
val _ = (print "bma_right29="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedR 2 9``))); print "\n");
val _ = (print "bma_right210="; print_term (boolSyntax.rhs(concl(EVAL ``almost_balancedR 2 10``))); print "\n");
