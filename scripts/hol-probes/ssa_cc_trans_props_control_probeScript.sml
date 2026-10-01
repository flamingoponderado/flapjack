load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory word_allocTheory wordSemTheory wordPropsTheory wordLangTheory sptreeTheory reg_allocTheory;
val _ = Globals.linewidth := 1000;
val is_alloc_var_add = prove (``  is_alloc_var na ⇒ is_alloc_var (na+4)``,
  full_simp_tac(srw_ss())[is_alloc_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]));
val is_stack_var_add = prove (``  is_stack_var na ⇒ is_stack_var (na+4)``,
  full_simp_tac(srw_ss())[is_stack_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]));
val is_alloc_var_flip = prove (``  is_alloc_var na ⇒ is_stack_var (na+2)``,
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  qspecl_then [`4`,`na`,`2`] assume_tac
    arithmeticTheory.MOD_PLUS >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []);
val is_stack_var_flip = prove (``  is_stack_var na ⇒ is_alloc_var (na+2)``,
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  qspecl_then [`4`,`na`,`2`] assume_tac
    arithmeticTheory.MOD_PLUS >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []);
val flip_rw = prove (``  is_stack_var(na+2) = is_alloc_var na ∧
    is_alloc_var(na+2) = is_stack_var na``,
  conj_tac >> (reverse EQ_TAC >-
    metis_tac[is_alloc_var_flip,is_stack_var_flip]) >>
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  mp_tac arithmeticTheory.MOD_PLUS >>
  (disch_then(qspecl_then[`4`,`na`,`2`](SUBST1_TAC o SYM)) >>
  `na MOD 4 < 4` by full_simp_tac(srw_ss())[]>>
  imp_res_tac (DECIDE ``n:num<4⇒(n=0)∨(n=1)∨(n=2)∨(n=3)``)>>
  full_simp_tac(srw_ss())[]));
val list_next_var_rename_props = prove (``  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'``,
  Induct>>full_simp_tac(srw_ss())[list_next_var_rename_def,next_var_rename_def]>>
  LET_ELIM_TAC>>
  first_x_assum(qspecl_then[`ssa''`,`na''`,`ys`,`ssa'''`,`na'''`]
    mp_tac)>>
  (impl_tac>-simp[] >>
   impl_tac >-
    (full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][]
    >-
      metis_tac[is_alloc_var_add,is_stack_var_add]
    >-
      (full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[convention_partitions])
    >-
      (full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
      res_tac>>DECIDE_TAC)))>>
  srw_tac[][]>> TRY(DECIDE_TAC)>> full_simp_tac(srw_ss())[]>>
  metis_tac[is_alloc_var_add,is_stack_var_add]);
val list_next_var_rename_move_props = prove (``  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename_move ssa na ls = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'``,
  full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>
  full_simp_tac(srw_ss())[]>>
  imp_res_tac list_next_var_rename_props);
val ssa_map_ok_more = prove (``  ssa_map_ok na ssa ∧ na ≤ na' ⇒
  ssa_map_ok na' ssa``,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][]
  >-
    metis_tac[]>>
  res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC);
val ssa_map_ok_lem = prove (``  ssa_map_ok na ssa ⇒ ssa_map_ok (na+2) ssa``,
  metis_tac[ssa_map_ok_more, DECIDE``na:num ≤ na+2``]);
val th =
  (MATCH_MP
    (PROVE[]``((a ⇒ b) ∧ (c ⇒ d)) ⇒ ((a ∨ c) ⇒ b ∨ d)``)
    (CONJ is_stack_var_flip is_alloc_var_flip))

val swap_imp =PROVE[]``A ==> B ==> C <=> B ==> A ==> C``

val list_next_var_rename_props_2 =
  list_next_var_rename_props
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["na","na'"]))
  |> Q.SPECL[`na+2`] |> SPEC_ALL
  |> UNDISCH
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> C MATCH_MP (UNDISCH th)
  |> DISCH_ALL
  |> REWRITE_RULE[flip_rw]
  |> ONCE_REWRITE_RULE [swap_imp]
  |> UNDISCH
  |> REWRITE_RULE[AND_IMP_INTRO]
  |> DISCH_ALL
  |> GEN_ALL
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["ls","ssa","na"]));

val list_next_var_rename_move_props_2 = prove (``  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename_move ssa (na+2) ls = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧ ssa_map_ok na ssa
  ⇒
  (na+2) ≤ na' ∧
  (is_alloc_var na ⇒ is_stack_var na') ∧
  (is_stack_var na ⇒ is_alloc_var na') ∧
  ssa_map_ok na' ssa'``,
  ntac 7 strip_tac>>imp_res_tac list_next_var_rename_move_props>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[is_stack_var_flip,is_alloc_var_flip,ssa_map_ok_lem]);
val ssa_map_ok_inter = prove (``  ssa_map_ok na ssa ⇒
  ssa_map_ok na (inter ssa ssa')``,
  full_simp_tac(srw_ss())[ssa_map_ok_def,lookup_inter]>>srw_tac[][]>>EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[]);
val ssa_map_ok_extend = GEN_ALL (prove (``  ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)``,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC));
val merge_moves_frame = GEN_ALL (prove (``  ∀ls na ssaL ssaR.
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
val fix_inconsistencies_props = GEN_ALL (prove (``  ∀ssaL ssaR na a b na' ssaU.
  fix_inconsistencies prio ssaL ssaR na = (a,b,na',ssaU) ==>
  is_alloc_var na ∧
  ssa_map_ok na ssaL ∧
  ssa_map_ok na ssaR
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssaU``,
  full_simp_tac(srw_ss())[fix_inconsistencies_def]>>LET_ELIM_TAC>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`var_union`] assume_tac)>>
  Q.ISPECL_THEN [`var_union`,`na''`,`ssa_L'`,`ssa_R'`] assume_tac fake_moves_frame>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  DECIDE_TAC));

val property = ``λprog ssa na lt. ∀progOut ssaOut naOut. ssa_cc_trans prog ssa na lt = (progOut,ssaOut,naOut) ⇒ ssa_map_ok na ssa ∧ is_alloc_var na ⇒ na ≤ naOut ∧ is_alloc_var naOut ∧ ssa_map_ok naOut ssaOut``;
val clauses = strip_conj(fst(dest_imp(concl(BETA_RULE(ISPEC property ssa_cc_trans_ind)))));
val case_7 = prove(List.nth(clauses,7), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>DECIDE_TAC));
val case_8 = prove(List.nth(clauses,8), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>DECIDE_TAC));
val case_9 = prove(List.nth(clauses,9), rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >> (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>imp_res_tac ssa_map_ok_more>>first_x_assum(qspec_then`na3` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>imp_res_tac fix_inconsistencies_props>>DECIDE_TAC));
fun out label th = (print(label ^ "="); print_thm th; print "\n");
val _ = out "spc_case_7" case_7;
val _ = out "spc_case_8" case_8;
val _ = out "spc_case_9" case_9;
fun vars t = if is_var t then [t] else if is_comb t then let val (a,b) = dest_comb t in vars a @ vars b end else if is_abs t then let val (a,b) = dest_abs t in a :: vars b end else [];
fun ty label name th = let val v=valOf(List.find(fn t => fst(dest_var t)=name)(vars(concl th))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = ty "spc_7_type_s1" "s1" case_7;
val _ = ty "spc_7_type_s2" "s2" case_7;
val _ = ty "spc_7_type_ssa" "ssa" case_7;
val _ = ty "spc_7_type_na" "na" case_7;
val _ = ty "spc_7_type_lt" "lt" case_7;
val _ = ty "spc_7_type_progOut" "progOut" case_7;
val _ = ty "spc_7_type_ssaOut" "ssaOut" case_7;
val _ = ty "spc_7_type_naOut" "naOut" case_7;
val _ = ty "spc_8_type_s1" "s1" case_8;
val _ = ty "spc_9_type_cmp" "cmp" case_9;
val _ = ty "spc_9_type_r1" "r1" case_9;
val _ = ty "spc_9_type_ri" "ri" case_9;
val _ = ty "spc_9_type_e2" "e2" case_9;
val _ = ty "spc_9_type_e3" "e3" case_9;
val _ = ty "spc_9_type_r1P" "r1'" case_9;
val _ = ty "spc_9_type_riP" "ri'" case_9;
val _ = ty "spc_9_type_e2P" "e2'" case_9;
val _ = ty "spc_9_type_ssa2" "ssa2" case_9;
val _ = ty "spc_9_type_na2" "na2" case_9;
