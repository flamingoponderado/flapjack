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
val ssa_map_ok_extend = prove (``  ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)``,
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC);
val props_alloc = prove (``∀num numset ssa na lt prog' ssa' na'. ssa_cc_trans (Alloc num numset) ssa na lt = (prog',ssa',na') ⇒ ssa_map_ok na ssa ∧ is_alloc_var na ⇒ na ≤ na' ∧ is_alloc_var na' ∧ ssa_map_ok na' ssa'``,
 rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >>
 full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    `∀naa. ssa_map_ok naa ssa''' ⇒ ssa_map_ok naa ssa_cut` by
      (srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[])>>
    `na ≤ na+2 ∧ na'' ≤ na''+2` by DECIDE_TAC>>
    imp_res_tac ssa_map_ok_more>>
    imp_res_tac list_next_var_rename_props_2>>
    imp_res_tac ssa_map_ok_more>>
    res_tac>>
    imp_res_tac list_next_var_rename_props_2>>
    DECIDE_TAC);
val result = props_alloc;
val _ = print "spa_alloc_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val vars = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vars) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "spa_alloc_type_num" "num";
val _ = out "spa_alloc_type_numset" "numset";
val _ = out "spa_alloc_type_ssa" "ssa";
val _ = out "spa_alloc_type_na" "na";
val _ = out "spa_alloc_type_lt" "lt";
val _ = out "spa_alloc_type_progOut" "prog'";
val _ = out "spa_alloc_type_ssaOut" "ssa'";
val _ = out "spa_alloc_type_naOut" "na'";
val props_install = prove (``∀ptr len dptr dlen numset ssa na lt prog' ssa' na'. ssa_cc_trans (Install ptr len dptr dlen numset) ssa na lt = (prog',ssa',na') ⇒ ssa_map_ok na ssa ∧ is_alloc_var na ⇒ na ≤ na' ∧ is_alloc_var na' ∧ ssa_map_ok na' ssa'``,
 rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >>
 rpt gen_tac>> strip_tac>>
    simp[Once (GSYM markerTheory.Abbrev_def)]>>
    qpat_x_assum`_= (_,_,_)` mp_tac>>LET_ELIM_TAC >>
    ( (* multiple goals *)
      fs[next_var_rename_def]>>rw[]>>
      imp_res_tac list_next_var_rename_move_props_2>>
      rw[]>>fs[]>>
      rfs[]>>
      qabbrev_tac`na2 = na''+2`>>
      `is_alloc_var na2` by fs[Abbr`na2`,is_stack_var_flip]>>
      rw[]>>
      qmatch_asmsub_abbrev_tac`list_next_var_rename_move sss _ _ = _`>>
      Q.ISPECL_THEN[`ls`,`sss`,`na''+6`] mp_tac list_next_var_rename_move_props>>
      simp[]>>
      `is_alloc_var (na2+4)` by metis_tac[is_alloc_var_add]>>
      `na''+6 = na2+4` by fs[Abbr`na2`]>>
      impl_tac>-
        (simp[Abbr`sss`,Abbr`ssa_cut`]>>
        match_mp_tac ssa_map_ok_extend>>
        CONJ_TAC>-
         (match_mp_tac ssa_map_ok_inter>>
         fs[Abbr`na2`]>>
         match_mp_tac (GEN_ALL ssa_map_ok_more)>>
         asm_exists_tac>>fs[])>>
        metis_tac[convention_partitions])>>
      strip_tac>>
      fs[Abbr`na2`,markerTheory.Abbrev_def]));
val result = props_install;
val _ = print "spa_install_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val vars = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vars) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "spa_install_type_ptr" "ptr";
val _ = out "spa_install_type_len" "len";
val _ = out "spa_install_type_dptr" "dptr";
val _ = out "spa_install_type_dlen" "dlen";
val _ = out "spa_install_type_numset" "numset";
val _ = out "spa_install_type_ssa" "ssa";
val _ = out "spa_install_type_na" "na";
val _ = out "spa_install_type_lt" "lt";
val _ = out "spa_install_type_progOut" "prog'";
val _ = out "spa_install_type_ssaOut" "ssa'";
val _ = out "spa_install_type_naOut" "na'";
val props_ffi = prove (``∀ffi_index ptr1 len1 ptr2 len2 numset ssa na lt prog' ssa' na'. ssa_cc_trans (FFI ffi_index ptr1 len1 ptr2 len2 numset) ssa na lt = (prog',ssa',na') ⇒ ssa_map_ok na ssa ∧ is_alloc_var na ⇒ na ≤ na' ∧ is_alloc_var na' ∧ ssa_map_ok na' ssa'``,
 rpt gen_tac >> full_simp_tac(srw_ss())[ssa_cc_trans_def] >>
 full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    `∀naa. ssa_map_ok naa ssa''' ⇒ ssa_map_ok naa ssa_cut` by
      (srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[])>>
    `na ≤ na+2 ∧ na'' ≤ na''+2` by DECIDE_TAC>>
    imp_res_tac ssa_map_ok_more>>
    imp_res_tac list_next_var_rename_props_2>>
    imp_res_tac ssa_map_ok_more>>
    res_tac>>
    imp_res_tac list_next_var_rename_props_2>>
    DECIDE_TAC);
val result = props_ffi;
val _ = print "spa_ffi_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val vars = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vars) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "spa_ffi_type_ffi_index" "ffi_index";
val _ = out "spa_ffi_type_ptr1" "ptr1";
val _ = out "spa_ffi_type_len1" "len1";
val _ = out "spa_ffi_type_ptr2" "ptr2";
val _ = out "spa_ffi_type_len2" "len2";
val _ = out "spa_ffi_type_numset" "numset";
val _ = out "spa_ffi_type_ssa" "ssa";
val _ = out "spa_ffi_type_na" "na";
val _ = out "spa_ffi_type_lt" "lt";
val _ = out "spa_ffi_type_progOut" "prog'";
val _ = out "spa_ffi_type_ssaOut" "ssa'";
val _ = out "spa_ffi_type_naOut" "na'";
