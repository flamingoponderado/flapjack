load "preamble";
load "reg_allocTheory";
open bossLib HolKernel Parse preamble reg_allocTheory;
val is_alloc_var_flip = GEN_ALL (prove (``is_alloc_var na ⇒ is_stack_var (na+2)``, full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  qspecl_then [`4`,`na`,`2`] assume_tac
    arithmeticTheory.MOD_PLUS >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []));
val is_stack_var_flip = GEN_ALL (prove (``is_stack_var na ⇒ is_alloc_var (na+2)``, full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  qspecl_then [`4`,`na`,`2`] assume_tac
    arithmeticTheory.MOD_PLUS >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []));
val flip_rw = GEN_ALL (prove (``is_stack_var(na+2) = is_alloc_var na ∧
    is_alloc_var(na+2) = is_stack_var na``, conj_tac >> (reverse EQ_TAC >-
    metis_tac[is_alloc_var_flip,is_stack_var_flip]) >>
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  mp_tac arithmeticTheory.MOD_PLUS >>
  (disch_then(qspecl_then[`4`,`na`,`2`](SUBST1_TAC o SYM)) >>
  `na MOD 4 < 4` by full_simp_tac(srw_ss())[]>>
  imp_res_tac (DECIDE ``n:num<4⇒(n=0)∨(n=1)∨(n=2)∨(n=3)``)>>
  full_simp_tac(srw_ss())[])));
fun out label q = (print(label ^ "=");print_term(rconc(EVAL q));print "\n");
fun theorem_out label th = let
 val _ = if null(hyp th) then () else raise Fail "undischarged original premise"
 in print(label ^ "=");print_term(rhs(concl(EQT_INTRO th)));print "\n" end;
fun guarded th n = let val t = SPECL [n] th in MATCH_MP t (EQT_ELIM(EVAL(fst(dest_imp(concl t))))) end;
val _ = out "rf_residue_0" ``(is_alloc_var 0,is_stack_var 0,is_alloc_var(0+2),is_stack_var(0+2))``;
val _ = theorem_out "rf_equalities_0" (SPECL [``0:num``] flip_rw);
val _ = out "rf_residue_1" ``(is_alloc_var 1,is_stack_var 1,is_alloc_var(1+2),is_stack_var(1+2))``;
val _ = theorem_out "rf_equalities_1" (SPECL [``1:num``] flip_rw);
val _ = out "rf_residue_2" ``(is_alloc_var 2,is_stack_var 2,is_alloc_var(2+2),is_stack_var(2+2))``;
val _ = theorem_out "rf_equalities_2" (SPECL [``2:num``] flip_rw);
val _ = out "rf_residue_3" ``(is_alloc_var 3,is_stack_var 3,is_alloc_var(3+2),is_stack_var(3+2))``;
val _ = theorem_out "rf_equalities_3" (SPECL [``3:num``] flip_rw);
val _ = out "rf_residue_4" ``(is_alloc_var 5,is_stack_var 5,is_alloc_var(5+2),is_stack_var(5+2))``;
val _ = theorem_out "rf_equalities_4" (SPECL [``5:num``] flip_rw);
val _ = out "rf_residue_5" ``(is_alloc_var 7,is_stack_var 7,is_alloc_var(7+2),is_stack_var(7+2))``;
val _ = theorem_out "rf_equalities_5" (SPECL [``7:num``] flip_rw);
val _ = out "rf_residue_6" ``(is_alloc_var 1000000000000000000000000000001,is_stack_var 1000000000000000000000000000001,is_alloc_var(1000000000000000000000000000001+2),is_stack_var(1000000000000000000000000000001+2))``;
val _ = theorem_out "rf_equalities_6" (SPECL [``1000000000000000000000000000001:num``] flip_rw);
val _ = out "rf_residue_7" ``(is_alloc_var 1000000000000000000000000000003,is_stack_var 1000000000000000000000000000003,is_alloc_var(1000000000000000000000000000003+2),is_stack_var(1000000000000000000000000000003+2))``;
val _ = theorem_out "rf_equalities_7" (SPECL [``1000000000000000000000000000003:num``] flip_rw);
val _ = theorem_out "rf_alloc_application_0" (guarded is_alloc_var_flip ``1:num``);
val _ = theorem_out "rf_alloc_application_1" (guarded is_alloc_var_flip ``5:num``);
val _ = theorem_out "rf_alloc_application_2" (guarded is_alloc_var_flip ``1000000000000000000000000000001:num``);
val _ = theorem_out "rf_stack_application_0" (guarded is_stack_var_flip ``3:num``);
val _ = theorem_out "rf_stack_application_1" (guarded is_stack_var_flip ``7:num``);
val _ = theorem_out "rf_stack_application_2" (guarded is_stack_var_flip ``1000000000000000000000000000003:num``);
val _ = (print "rf_is_alloc_var_flip_source_replay=";print_thm is_alloc_var_flip;print "\n");
val _ = (print "rf_is_stack_var_flip_source_replay=";print_thm is_stack_var_flip;print "\n");
val _ = (print "rf_flip_rw_source_replay=";print_thm flip_rw;print "\n");
