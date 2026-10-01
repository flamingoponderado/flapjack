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
val property = ``λprog ssa na lt. ∀progOut ssaOut naOut. ssa_cc_trans prog ssa na lt = (progOut,ssaOut,naOut) ⇒ ssa_map_ok na ssa ∧ is_alloc_var na ⇒ na ≤ naOut ∧ is_alloc_var naOut ∧ ssa_map_ok naOut ssaOut``;
val specialized = BETA_RULE (ISPEC property ssa_cc_trans_ind);
val clauses = strip_conj (fst (dest_imp (concl specialized)));
val props_Loop = prove (List.nth (clauses, 24),
 rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >>
   strip_tac >>
  LET_ELIM_TAC >>
  fs[loop_setup_def] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  rveq >>
  drule_then assume_tac list_next_var_rename_props >>
  rfs[] >>
  qpat_x_assum `list_next_var_rename_move _ _ _ = _` assume_tac >>
  drule_then assume_tac list_next_var_rename_move_props >>
  rfs[] >>
  unabbrev_all_tac >>
  `ssa_map_ok na_refreshed (inter ssa_refreshed names)` by
    (match_mp_tac ssa_map_ok_inter >> first_x_assum ACCEPT_TAC) >>
  qpat_x_assum `_ ∧ is_alloc_var na_refreshed ⇒ _` mp_tac >>
  impl_tac >- simp[] >>
  strip_tac >>
  rpt conj_tac >>
  TRY (match_mp_tac ssa_map_ok_inter >>
       irule ssa_map_ok_more >>
       qexists_tac `na_refreshed`) >>
  gs[]);
val result = props_Loop;
val _ = print "spl_full="; val _ = print_thm result; val _ = print "\n";
fun vars t = if is_var t then [t] else if is_comb t then let val (f,x) = dest_comb t in vars f @ vars x end else if is_abs t then let val (v,b) = dest_abs t in v :: vars b end else [];
fun out label name = let val v = valOf(List.find (fn t => fst(dest_var t) = name) (vars(concl result))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "spl_type_names" "names";
val _ = out "spl_type_body" "body";
val _ = out "spl_type_exit_names" "exit_names";
val _ = out "spl_type_ssa" "ssa";
val _ = out "spl_type_na" "na";
val _ = out "spl_type_lt" "lt";
val _ = out "spl_type_progOut" "progOut";
val _ = out "spl_type_ssaOut" "ssaOut";
val _ = out "spl_type_naOut" "naOut";
val _ = out "spl_type_setup_prog" "setup_prog";
val _ = out "spl_type_ssa_refreshed" "ssa_refreshed";
val _ = out "spl_type_na_refreshed" "na_refreshed";
val _ = out "spl_type_ssa_names" "ssa_names";
val _ = out "spl_type_ssa_exit" "ssa_exit";
val _ = out "spl_type_ssa_body" "ssa_body";
val props_Break = prove (List.nth (clauses, 25),
 rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >>
   fs[ssa_cc_trans_def]>>every_case_tac>>fs[]>>rveq>>simp[]);
val result = props_Break;
val _ = print "spb_full="; val _ = print_thm result; val _ = print "\n";
fun vars t = if is_var t then [t] else if is_comb t then let val (f,x) = dest_comb t in vars f @ vars x end else if is_abs t then let val (v,b) = dest_abs t in v :: vars b end else [];
fun out label name = let val v = valOf(List.find (fn t => fst(dest_var t) = name) (vars(concl result))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "spb_type_n" "n";
val _ = out "spb_type_ssa" "ssa";
val _ = out "spb_type_na" "na";
val _ = out "spb_type_lt" "lt";
val _ = out "spb_type_progOut" "progOut";
val _ = out "spb_type_ssaOut" "ssaOut";
val _ = out "spb_type_naOut" "naOut";
val props_Continue = prove (List.nth (clauses, 26),
 rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >>
   fs[ssa_cc_trans_def]>>every_case_tac>>fs[]>>rveq>>simp[]);
val result = props_Continue;
val _ = print "spc_full="; val _ = print_thm result; val _ = print "\n";
fun vars t = if is_var t then [t] else if is_comb t then let val (f,x) = dest_comb t in vars f @ vars x end else if is_abs t then let val (v,b) = dest_abs t in v :: vars b end else [];
fun out label name = let val v = valOf(List.find (fn t => fst(dest_var t) = name) (vars(concl result))) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "spc_type_n" "n";
val _ = out "spc_type_ssa" "ssa";
val _ = out "spc_type_na" "na";
val _ = out "spc_type_lt" "lt";
val _ = out "spc_type_progOut" "progOut";
val _ = out "spc_type_ssaOut" "ssaOut";
val _ = out "spc_type_naOut" "naOut";
