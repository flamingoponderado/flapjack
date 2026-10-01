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
val result = list_next_var_rename_props_2;
val _ = print "srl_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val vars = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vars) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "srl_type_ls" "ls";
val _ = out "srl_type_ssa" "ssa";
val _ = out "srl_type_na" "na";
val _ = out "srl_type_lsOut" "ls'";
val _ = out "srl_type_ssaOut" "ssa'";
val _ = out "srl_type_naOut" "na'";
val result = list_next_var_rename_move_props_2;
val _ = print "srm_full="; val _ = print_thm result; val _ = print "\n";
fun out label name = let val vars = fst(strip_forall(concl result)) @ free_vars(concl result); val v = valOf(List.find (fn t => fst(dest_var t) = name) vars) in print(label ^ "="); print_type(type_of v); print "\n" end;
val _ = out "srm_type_ls" "ls";
val _ = out "srm_type_ssa" "ssa";
val _ = out "srm_type_na" "na";
val _ = out "srm_type_lsOut" "ls'";
val _ = out "srm_type_ssaOut" "ssa'";
val _ = out "srm_type_naOut" "na'";
