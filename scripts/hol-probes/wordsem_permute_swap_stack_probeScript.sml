load "preamble"; load "helperLib"; load "wordPropsTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib mllistTheory backendPropsTheory wordConvsTheory wordLangTheory wordSemTheory asmTheory reg_allocTheory wordPropsTheory;
val _ = Globals.linewidth := 1000000;
(* Script-local helper vals copied verbatim from wordPropsScript.sml:43-49. *)
val GENLIST_I =
  GENLIST_EL |> Q.SPECL [`xs`,`\i. EL i xs`,`LENGTH xs`]
    |> SIMP_RULE std_ss []
val ALL_DISTINCT_EL = ``ALL_DISTINCT xs``
  |> ONCE_REWRITE_CONV [GSYM GENLIST_I]
  |> SIMP_RULE std_ss [ALL_DISTINCT_GENLIST]
fun check name th original =
  if null(hyp th) andalso null(free_vars(concl th)) andalso aconv (concl th) (concl(GEN_ALL original))
  then () else raise Fail ("replay " ^ name);
(* permute_swap_lemma2 uses suspend/resume; its closed statement is captured.
   rich_list list_rel_lastn is a HOL library theorem, captured likewise. *)
val _ = if null(hyp permute_swap_lemma2) andalso null(free_vars(concl(GEN_ALL permute_swap_lemma2))) then () else raise Fail "open lemma2";
val _ = (print "permute_swap_lemma2_statement="; print_term(concl(GEN_ALL permute_swap_lemma2)); print "\n");
val _ = (print "list_rel_lastn_statement="; print_term(concl(GEN_ALL rich_listTheory.list_rel_lastn)); print "\n");
val perm_list_rearrange_replay = GEN_ALL(prove(concl PERM_list_rearrange,
  srw_tac[][] \\ match_mp_tac PERM_ALL_DISTINCT
  \\ full_simp_tac(srw_ss())[mem_list_rearrange]
  \\ full_simp_tac(srw_ss())[wordSemTheory.list_rearrange_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[ALL_DISTINCT_GENLIST] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF,SURJ_DEF]
  \\ full_simp_tac(srw_ss())[ALL_DISTINCT_EL]));
val _ = check "PERM_list_rearrange" perm_list_rearrange_replay PERM_list_rearrange;
val _ = (print "PERM_list_rearrange_statement="; print_term(concl perm_list_rearrange_replay); print "\n");
val _ = print("PERM_list_rearrange_hypotheses=" ^ Int.toString(length(hyp perm_list_rearrange_replay)) ^ "\n");
val all_distinct_mem_imp_alookup_some_replay = GEN_ALL(prove(concl ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME,
  map_every qid_spec_tac [‘x’, ‘y’] >> Induct_on ‘xs’ >>
  full_simp_tac(srw_ss())[]
  \\ Cases \\ full_simp_tac(srw_ss())[ALOOKUP_def] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[MEM_MAP,FORALL_PROD]
  \\ rev_full_simp_tac(srw_ss())[]));
val _ = check "ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME" all_distinct_mem_imp_alookup_some_replay ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME;
val _ = show_types := true;
val _ = (print "ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME_types="; print_term(concl all_distinct_mem_imp_alookup_some_replay); print "\n");
val _ = show_types := false;
val _ = (print "ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME_statement="; print_term(concl all_distinct_mem_imp_alookup_some_replay); print "\n");
val _ = print("ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME_hypotheses=" ^ Int.toString(length(hyp all_distinct_mem_imp_alookup_some_replay)) ^ "\n");
val env_to_list_all_distinct_replay = GEN_ALL(prove(concl env_to_list_ALL_DISTINCT,
  fs [wordSemTheory.env_to_list_def] \\ rw []
  \\ qmatch_goalsub_abbrev_tac `list_rearrange _ l`
  \\ `PERM (toAList y) l` by fs [Abbr`l`,sort_PERM]
  \\ qsuff_tac `PERM l (list_rearrange (perm 0) l)`
  THEN1
   (strip_tac
    \\ `PERM (toAList y) (list_rearrange (perm 0) l)` by imp_res_tac PERM_TRANS
    \\ drule (Q.ISPEC `FST` sortingTheory.PERM_MAP) \\ strip_tac
    \\ drule (GSYM ALL_DISTINCT_PERM) \\ fs [ALL_DISTINCT_MAP_FST_toAList])
  \\ match_mp_tac PERM_list_rearrange
  \\ drule (GSYM ALL_DISTINCT_PERM) \\ fs [] \\ rw []
  \\ match_mp_tac (Q.ISPEC `FST` listTheory.ALL_DISTINCT_MAP)
  \\ fs [ALL_DISTINCT_MAP_FST_toAList]));
val _ = check "env_to_list_ALL_DISTINCT" env_to_list_all_distinct_replay env_to_list_ALL_DISTINCT;
val _ = (print "env_to_list_ALL_DISTINCT_statement="; print_term(concl env_to_list_all_distinct_replay); print "\n");
val _ = print("env_to_list_ALL_DISTINCT_hypotheses=" ^ Int.toString(length(hyp env_to_list_all_distinct_replay)) ^ "\n");
val env_to_list_all_distinct_fst_replay = GEN_ALL(prove(concl env_to_list_ALL_DISTINCT_FST,
  Cases_on ‘env_to_list y perm’ >>
  metis_tac[env_to_list_ALL_DISTINCT,FST]));
val _ = check "env_to_list_ALL_DISTINCT_FST" env_to_list_all_distinct_fst_replay env_to_list_ALL_DISTINCT_FST;
val _ = (print "env_to_list_ALL_DISTINCT_FST_statement="; print_term(concl env_to_list_all_distinct_fst_replay); print "\n");
val _ = print("env_to_list_ALL_DISTINCT_FST_hypotheses=" ^ Int.toString(length(hyp env_to_list_all_distinct_fst_replay)) ^ "\n");
val perm_fromalist_replay = GEN_ALL(prove(concl PERM_fromAList,
  rw[] >>
  dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm] >>
  simp[wf_fromAList] >>
  simp[lookup_fromAList] >>
  rw[] >>
  Cases_on ‘ALOOKUP l2 n’
  >- (dxrule MEM_PERM >> strip_tac >> gvs[ALOOKUP_NONE,MEM_MAP]) >>
  drule_then assume_tac ALOOKUP_MEM >>
  match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
  metis_tac[MEM_PERM]));
val _ = check "PERM_fromAList" perm_fromalist_replay PERM_fromAList;
val _ = (print "PERM_fromAList_statement="; print_term(concl perm_fromalist_replay); print "\n");
val _ = print("PERM_fromAList_hypotheses=" ^ Int.toString(length(hyp perm_fromalist_replay)) ^ "\n");
val stack_size_perm_replay = GEN_ALL(prove(concl stack_size_perm,
  ho_match_mp_tac LIST_REL_ind >>
  rw[] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  fs[stack_size_eq2] >>
  rename1 ‘StackFrame _ _ _ handler’ >>
  Cases_on ‘handler’ >>
  gvs[stack_size_frame_def]));
val _ = check "stack_size_perm" stack_size_perm_replay stack_size_perm;
val _ = (print "stack_size_perm_statement="; print_term(concl stack_size_perm_replay); print "\n");
val _ = print("stack_size_perm_hypotheses=" ^ Int.toString(length(hyp stack_size_perm_replay)) ^ "\n");
val env_to_list_perm_replay = GEN_ALL(prove(concl env_to_list_PERM,
  rw[env_to_list_def] \\
  match_mp_tac PERM_TRANS \\
  qspec_then ‘env’ assume_tac ALL_DISTINCT_MAP_FST_toAList \\
  drule_then assume_tac ALL_DISTINCT_MAP \\
  irule_at (Pos last) PERM_list_rearrange \\
  ‘PERM (toAList env) (sort key_val_compare (toAList env))’
    by(MATCH_ACCEPT_TAC sort_PERM) \\
  conj_asm1_tac THEN1 metis_tac[ALL_DISTINCT_PERM] \\
  simp[Once PERM_SYM] \\
  match_mp_tac PERM_list_rearrange \\
  simp[]));
val _ = check "env_to_list_PERM" env_to_list_perm_replay env_to_list_PERM;
val _ = (print "env_to_list_PERM_statement="; print_term(concl env_to_list_perm_replay); print "\n");
val _ = print("env_to_list_PERM_hypotheses=" ^ Int.toString(length(hyp env_to_list_perm_replay)) ^ "\n");
val permute_swap_lemma3_replay = GEN_ALL(prove(concl permute_swap_lemma3,
  rw[] >>
  pairarg_tac >>
  rw[] >>
  qspecl_then [‘prog’,‘st’,‘perm’,‘st.stack’] assume_tac permute_swap_lemma2 >>
  gvs[] >>
  pop_assum mp_tac >> impl_tac
  >- (rename1 ‘LIST_REL _ l’ >> Induct_on ‘l’ >>
      rw[] >> TOP_CASE_TAC >> gvs[]) >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_,st1)’ >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_,st2)’ >>
  ‘st1 = st2’ by rw[Abbr ‘st1’, Abbr ‘st2’, state_component_equality] >>
  gvs[] >>
  simp[state_component_equality]));
val _ = check "permute_swap_lemma3" permute_swap_lemma3_replay permute_swap_lemma3;
val _ = (print "permute_swap_lemma3_statement="; print_term(concl permute_swap_lemma3_replay); print "\n");
val _ = print("permute_swap_lemma3_hypotheses=" ^ Int.toString(length(hyp permute_swap_lemma3_replay)) ^ "\n");
