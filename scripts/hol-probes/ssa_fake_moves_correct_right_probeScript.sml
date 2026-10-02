load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val ssa_map_ok_extend = prove (``  ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)``,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC);
val fake_moves_frame = prove (``  ∀ls na ssaL ssaR.
  is_alloc_var na
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')``,
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  (CONJ_TAC>-
    (full_simp_tac(srw_ss())[is_alloc_var_def]>>
    (assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`4`,`r1`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions]);
val fake_moves_correctR = prove (``  ∀ls na ssaL ssaR stR cstR.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaR
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  (ssa_locals_rel na ssaR stR.locals cstR.locals ⇒
  let (resR,rcstR) = evaluate(moveR,cstR) in
    resR = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaR' = lookup x ssaR) ∧
    (∀x y. (x < na ∧ lookup x cstR.locals = SOME y)
    ⇒  lookup x rcstR.locals = SOME y) ∧
    ssa_locals_rel na' ssaR' stR.locals rcstR.locals ∧
    word_state_eq_rel cstR rcstR)``,
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
  (srw_tac[][]>>
  full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
  rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stR`,`cstR`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[evaluate_def,LET_THM,evaluate_def,fake_move_def,word_exp_def,inst_def,assign_def]>>
  Cases_on`evaluate(r0,cstR)`>>full_simp_tac(srw_ss())[]>>
  `na ≤ r1 ∧ ssa_map_ok r1 r3` by
    (imp_res_tac fake_moves_frame>>
    full_simp_tac(srw_ss())[LET_THM]>>
    pop_assum(qspecl_then[`ssaR`,`ssaL`,`prio`,`ls`]assume_tac)>>rev_full_simp_tac(srw_ss())[])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,set_var_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
        (res_tac>>full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,get_vars_def,get_var_def,set_vars_def,alist_insert_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h r3 = SOME v'''` SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v''' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v''' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]));
val result = fake_moves_correctR;
val _ = print "fmr_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val vars = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vars) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "fmr_type_ls" "ls";
val _ = out "fmr_type_na" "na";
val _ = out "fmr_type_ssaL" "ssaL";
val _ = out "fmr_type_ssaR" "ssaR";
val _ = out "fmr_type_stR" "stR";
val _ = out "fmr_type_cstR" "cstR";
val _ = out "fmr_type_prio" "prio";
