load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val ssa_map_ok_extend = GEN_ALL (prove (``ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)``,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC));
val merge_moves_frame = GEN_ALL (prove (``∀ls na ssaL ssaR.
  is_alloc_var na
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')``,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
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
  metis_tac[ssa_map_ok_extend,convention_partitions]));
val merge_moves_fst = GEN_ALL (prove (``∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  na ≤ na' ∧
  EVERY (λx. x < na' ∧ x ≥ na) (MAP FST moveL) ∧
  EVERY (λx. x < na' ∧ x ≥ na) (MAP FST moveR)``,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[EVERY_MAP]>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`]assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  qpat_x_assum`A = moveL` (sym_sub_tac)>>
  qpat_x_assum`A = moveR` (sym_sub_tac)>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>srw_tac[][]>>
  res_tac>>
  DECIDE_TAC));
val mov_eval_head = GEN_ALL (prove (``evaluate(Move p moves,st) = (NONE,rst) ∧
  y ∈ domain st.locals ∧
  ¬MEM y (MAP FST moves) ∧
  ¬MEM x (MAP FST moves)
  ⇒
  evaluate(Move p ((x,y)::moves),st) = (NONE, rst with locals:=insert x (THE (lookup y st.locals)) rst.locals)``,
  full_simp_tac(srw_ss())[evaluate_def,get_vars_def,get_var_def,domain_lookup]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>
  full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
  qpat_x_assum `A=rst` (sym_sub_tac)>>full_simp_tac(srw_ss())[]));
val merge_moves_correctL = GEN_ALL (prove (``∀ls na ssaL ssaR stL cstL pri.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaL
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaL stL.locals cstL.locals ⇒
  let (resL,rcstL) = evaluate(Move pri moveL,cstL) in
    resL = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaL' = lookup x ssaL) ∧
    (∀x y. (x < na ∧ lookup x cstL.locals = SOME y)
    ⇒  lookup x rcstL.locals = SOME y) ∧
    ssa_locals_rel na' ssaL' stL.locals rcstL.locals ∧
    word_state_eq_rel cstL rcstL)``,
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
  (srw_tac[][]>>
  full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
  rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stL`,`cstL`,`pri`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  Cases_on`evaluate(Move pri q,cstL)`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_fst>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  imp_res_tac mov_eval_head>>
  pop_assum(qspec_then`r1` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM]>>
    res_tac>>
    DECIDE_TAC)>>
  strip_tac>>
  pop_assum(qspec_then`x'` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM,ssa_map_ok_def]>>
    res_tac>>
    DECIDE_TAC)>>
  impl_tac>-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    metis_tac[])>>
  strip_tac>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
  >-
    (`x'' ≠ r1` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[lookup_insert])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h ssaL = SOME x'` (SUBST_ALL_TAC)>>
      full_simp_tac(srw_ss())[])>>
      res_tac>>
      full_simp_tac(srw_ss())[domain_lookup]>>
       `v'' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>DECIDE_TAC))
  >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]));
val _ = print "mlc_full=";
val _ = print_thm merge_moves_correctL;
val _ = print "\n";
fun out label name = let val v = valOf(List.find (fn t => fst(dest_var t) = name) (fst(strip_forall(concl merge_moves_correctL)))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "mlc_type_ls" "ls";
val _ = out "mlc_type_na" "na";
val _ = out "mlc_type_ssaL" "ssaL";
val _ = out "mlc_type_ssaR" "ssaR";
val _ = out "mlc_type_stL" "stL";
val _ = out "mlc_type_cstL" "cstL";
val _ = out "mlc_type_pri" "pri";
