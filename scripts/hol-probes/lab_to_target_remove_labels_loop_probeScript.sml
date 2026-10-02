load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory labSemTheory sptreeTheory backendPropsTheory asmPropsTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val case_eq_thms0 = map TypeBase.case_eq_of [``:lab``, ``:'a option``];
val bool_case_eq_thms = map (fn th =>
  let val v = th |> concl |> lhs |> rhs
  in th |> GEN v |> Q.ISPEC`T` |> SIMP_RULE bool_ss [] end) case_eq_thms0;
val enc_lines_again_all_enc_ok_pre = Q.prove(`  ∀labs ffis pos enc lines acc ok res ok' c.
  enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') ∧
  EVERY (line_ok_pre c) lines ∧ EVERY (line_ok_pre c) acc ⇒
  EVERY (line_ok_pre c) res`,
  recInduct enc_lines_again_ind>>rw[enc_lines_again_def]>>
  rw[EVERY_REVERSE]>>fs[line_ok_pre_def]);
val enc_secs_again_all_enc_ok_pre = Q.prove(`  ∀pos labs ffis enc ls res ok c.
  enc_secs_again pos labs ffis enc ls = (res,ok) ∧ all_enc_ok_pre c ls ⇒
  all_enc_ok_pre c res`,
  ho_match_mp_tac enc_secs_again_ind>>rw[enc_secs_again_def]>>
  rw[]>>
  rpt (pairarg_tac>>fs[])>>
  rw[]>>
  match_mp_tac enc_lines_again_all_enc_ok_pre>>asm_exists_tac>>fs[]);
val line_ok_pre_add_nop = Q.prove(`  EVERY (line_ok_pre c) xs ⇒
  EVERY (line_ok_pre c) (add_nop nop xs)`,
  Induct_on`xs`>>EVAL_TAC>>Cases>>fs[]>>rw[]>>EVAL_TAC>>fs[line_ok_pre_def]);
val line_ok_pre_pad_section = Q.prove(`  ∀nop xs acc c.
  EVERY (line_ok_pre c) xs ∧ EVERY (line_ok_pre c) acc ⇒
  EVERY (line_ok_pre c) (pad_section nop xs acc)`,
  ho_match_mp_tac pad_section_ind>>rw[pad_section_def]>>
  fs[EVERY_REVERSE]>>
  first_x_assum match_mp_tac>>fs[line_ok_pre_def]>>
  metis_tac[line_ok_pre_add_nop]);
val all_enc_ok_pre_pad_code = Q.prove(`  ∀nop code c.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (pad_code nop code)`,
  ho_match_mp_tac pad_code_ind>>rw[]>>EVAL_TAC>>rw[]>>
  rfs[]>>
  match_mp_tac line_ok_pre_pad_section>>fs[]);
val all_enc_ok_pre_lines_upd_lab_len = Q.prove(`  ∀n lines acc.
  EVERY (line_ok_pre c) lines ∧
  EVERY (line_ok_pre c) acc ⇒
  EVERY (line_ok_pre c) (FST (lines_upd_lab_len n lines acc))`,
  ho_match_mp_tac lines_upd_lab_len_ind>>rw[lines_upd_lab_len_def]>>
  fs[EVERY_REVERSE,line_ok_pre_def]);
val all_enc_ok_pre_upd_lab_len = Q.prove(`  ∀n code.
  all_enc_ok_pre c code ⇒
  all_enc_ok_pre c (upd_lab_len n code)`,
  ho_match_mp_tac upd_lab_len_ind>>rw[]>> EVAL_TAC>>fs[]>>
  pairarg_tac \\ fs[] \\
  qspecl_then[`n`,`lines`,`[]`]mp_tac all_enc_ok_pre_lines_upd_lab_len
  \\ rw[]);
val lab_lookup_IMP = Q.prove(`  (lab_lookup l1 l2 labs = SOME x) ==>
    (find_pos (Lab l1 l2) labs = x)`,
  full_simp_tac(srw_ss())[lab_lookup_def,find_pos_def,lookup_any_def]
  \\ BasicProvers.EVERY_CASE_TAC);
val all_enc_ok_even = Q.prove(`  ∀lines pos.
  all_enc_ok c labs ffis pos [Section k lines] ⇒
  EVEN (sec_length lines pos)`,
  Induct>>fs[all_enc_ok_def,sec_length_def]>>Cases>>
  TRY(Cases_on`a`)>>
  rw[]>>fs[line_ok_def,line_length_def,sec_length_add,sec_length_def]>>
  rfs[]>>
  `n + sec_length lines pos = sec_length lines (n + pos)` by
    metis_tac[sec_length_add,ADD_COMM]>>
  fs[]>>
  fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[]);
val all_enc_ok_split = Q.prove(`  ∀c labs ffis pos k lines xs.
  all_enc_ok c labs ffis pos (Section k lines::xs) ⇒
  all_enc_ok c labs ffis pos [Section k lines] ∧
  all_enc_ok c labs ffis (pos + sec_length lines 0) xs`,
  Induct_on`lines`>>rw[all_enc_ok_def,sec_length_def,all_enc_ok_def]>>
  Cases_on`h`>>TRY(Cases_on`a`)>>
  fs[sec_length_def,sec_length_add,line_length_def,line_ok_def]>>rveq>>
  fs(bool_case_eq_thms) \\ imp_res_tac lab_lookup_IMP \\ rw[] >>
  rfs[]>>
  metis_tac[ADD_ASSOC]);
val all_enc_ok_lab_lookup_even = Q.prove(`  ∀c labs ffis pos sec_list l1 l2 acc x.
      all_enc_ok c labs ffis pos sec_list ∧
      lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) = SOME x ∧
      (∀x. lab_lookup l1 l2 acc = SOME x ==> EVEN x) ∧
      EVEN pos ⇒
      EVEN x`,
  Induct_on`sec_list`>>
  fs[all_enc_ok_def,compute_labels_alt_def]>>
  Cases \\ fs[compute_labels_alt_def] \\
  rw[] \\
  imp_res_tac all_enc_ok_split
  \\ pairarg_tac \\ fs[]
  \\ last_x_assum(match_mp_tac o MP_CANON)
  \\ fs[]
  \\ asm_exists_tac \\ fs[]
  \\ imp_res_tac all_enc_ok_even
  \\ qspecl_then[`pos`,`l`,`[]`]mp_tac section_labels_sec_length \\ rw[]
  \\ qspecl_then[`l`,`0`,`pos`]mp_tac sec_length_add \\ rw[] \\ fs[]
  \\ asm_exists_tac \\ fs[EVEN_ADD]
  \\ rw[lab_lookup_def,lookup_insert]
  \\ fs[lookup_fromAList]
  \\ pop_assum mp_tac \\ rw[] \\ fs[]
  \\ fs[all_enc_ok_cons]
  \\ match_mp_tac lines_ok_section_lab_lookup_even
  \\ asm_exists_tac \\ fs[]
  \\ qexists_tac`[]` \\ simp[]);
val lab_lookup_compute_labels_test = Q.prove(`  ∀pos sec_list acc l1 l2 x2 c labs ffis nop.
      EVERY sec_labels_ok sec_list /\
      ALL_DISTINCT (MAP Section_num sec_list) ∧
      EVERY (ALL_DISTINCT o extract_labels o Section_lines) sec_list ∧
      EVERY sec_label_zero sec_list /\
      all_enc_ok c labs ffis pos sec_list /\
      loc_to_pc l1 l2 sec_list = SOME x2 ==>
      lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) =
      SOME (pos_val x2 pos sec_list)`,
  ho_match_mp_tac compute_labels_alt_ind>>fs[]>>
  CONJ_TAC >- (rw[]>> fs[compute_labels_alt_def,loc_to_pc_def])
  \\ rw[compute_labels_alt_def,pos_val_thm]
  \\ pop_assum mp_tac
  \\ simp[Once loc_to_pc_thm]
  \\ pairarg_tac \\ fs[]
  \\ fs[all_enc_ok_cons]
  \\ old_drule lines_ok_lines_enc_with_nop \\ strip_tac
  \\ old_drule lines_enc_with_nop_length_ok \\ strip_tac
  \\ IF_CASES_TAC \\ fs[]
  >- (
    rveq
    \\ TOP_CASE_TAC
    >- (
      Cases_on`loc_to_pc k l2 sec_list` \\ fs[]
      \\ strip_tac \\ rveq
      \\ qmatch_goalsub_abbrev_tac`sec_pos_val i pos lines`
      \\ qspecl_then[`i`,`pos`,`lines`]mp_tac sec_pos_val_too_big
      \\ impl_tac >- simp[Abbr`i`]
      \\ simp[] \\ strip_tac
      \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac section_labels_sec_length \\ rw[]
      \\ qspecl_then[`lines`,`pos`]mp_tac sec_length_sum_line_length \\ rw[] \\ fs[]
      \\ first_x_assum match_mp_tac \\ asm_exists_tac \\ fs[])
    \\ strip_tac \\ rveq
    \\ simp[lab_lookup_compute_labels_alt_ignore]
    \\ simp[lab_lookup_def]
    \\ Cases_on`l2=0`
    >- (
      simp[lookup_fromAList]
      \\ fs[Once sec_loc_to_pc_def]
      \\ rveq
      \\ imp_res_tac lines_enc_with_nop_label_zero
      \\ Cases_on`EVERY is_Label lines`
      >- (
        `FILTER ($~ o is_Label) lines = []`
        by srw_tac[ETA_ss][FILTER_EQ_NIL] \\ simp[]
        \\ simp[EVERY_is_Label_sec_pos_val]
        \\ imp_res_tac pos_val_0 \\ simp[]
        \\ `SUM (MAP line_length lines) = 0` suffices_by simp[]
        \\ rw[SUM_eq_0,MEM_MAP] \\ fs[EVERY_MEM]
        \\ res_tac
        \\ Cases_on`y` \\ fs[line_length_def] )
      \\ imp_res_tac sec_pos_val_0
      \\ simp[] )
    \\ simp[lookup_fromAList]
    \\ old_drule (GEN_ALL ALOOKUP_section_labels)
    \\ fs[sec_label_zero_def]
    \\ disch_then old_drule \\ simp[]
    \\ disch_then(qspecl_then[`pos`,`[]`]strip_assume_tac) \\ rfs[]
    \\ match_mp_tac EQ_SYM
    \\ simp[lookup_insert, lookup_fromAList]
    \\ match_mp_tac pos_val_0
    \\ asm_exists_tac \\ fs[])
  \\ strip_tac
  \\ rveq
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`sec_pos_val i pos lines`
  \\ qspecl_then[`i`,`pos`,`lines`]mp_tac sec_pos_val_too_big
  \\ impl_tac >- simp[Abbr`i`]
  \\ simp[] \\ strip_tac
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac section_labels_sec_length \\ rw[]
  \\ qspecl_then[`lines`,`pos`]mp_tac sec_length_sum_line_length \\ rw[] \\ fs[]
  \\ first_x_assum match_mp_tac \\ asm_exists_tac \\ fs[]);
val remove_labels_loop_thm = Q.prove(`  ∀n c init_pos init_labs ffis code code2 labs.
    remove_labels_loop n c init_pos init_labs ffis code = SOME (code2,labs) ∧
    EVERY sec_ends_with_label code ∧
    EVERY sec_labels_ok code ∧
    ALL_DISTINCT (MAP Section_num code) ∧
    EVERY (ALL_DISTINCT o extract_labels o Section_lines) code ∧
    DISJOINT (domain init_labs) (set (MAP Section_num code)) ∧
    (* TODO this is stronger:
      get_labels code ⊆ get_code_labels code ∪ labs_domain init_labs ∧
    *)
    restrict_nonzero (get_labels code) ⊆ get_code_labels code ∪ labs_domain init_labs ∧
    all_enc_ok_pre c code ∧ (* new loop invariant *)
    all_encd0 c.encode code ∧
    enc_ok c ∧
    EVEN init_pos ∧
    (!l1 l2. OPTION_ALL EVEN (lab_lookup l1 l2 init_labs))
    ⇒
    all_enc_ok_pre c code2 ∧
    EVERY sec_labels_ok code2 ∧
    all_enc_ok c labs ffis init_pos code2 /\
    code_similar code code2 /\
    (has_odd_inst code2 ⇒ c.code_alignment = 0) /\
    (!l1 l2 x. lab_lookup l1 l2 labs = SOME x ==> EVEN x) /\
    (!l1 l2 x. lab_lookup l1 l2 init_labs = SOME x ==>
               lab_lookup l1 l2 labs = SOME x) /\
    !l1 l2 x2.
      loc_to_pc l1 l2 code = SOME x2 ==>
      lab_lookup l1 l2 labs = SOME (pos_val x2 init_pos code2)`,
  HO_MATCH_MP_TAC remove_labels_loop_ind  >> rpt gen_tac >> strip_tac
  >> simp[Once remove_labels_loop_def]
  >> rpt gen_tac
  >> pairarg_tac \\ fs []
  >> reverse IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  >> strip_tac >> rveq THEN1
   (   fs[]
    >> last_x_assum mp_tac
    >> impl_tac >- (
      srw_tac[][]
      >- (
        match_mp_tac enc_secs_again_ends_with_label
        \\ metis_tac[] )
      >- (match_mp_tac enc_secs_again_sec_labels_ok>>metis_tac[])
      >- (metis_tac[code_similar_MAP_Section_num,enc_secs_again_IMP_similar])
      >- (fs[GSYM ALL_EL_MAP]
          \\ metis_tac[enc_secs_again_IMP_similar,code_similar_extract_labels])
      >- (metis_tac[code_similar_MAP_Section_num,enc_secs_again_IMP_similar])
      >- (metis_tac[code_similar_get_labels, code_similar_get_code_labels, enc_secs_again_IMP_similar])
      >- (match_mp_tac enc_secs_again_all_enc_ok_pre>>metis_tac[])
      >- (match_mp_tac enc_secs_again_encd0 \\ metis_tac[] ))
    >> simp[] >> strip_tac >> fs []
    >> old_drule enc_secs_again_IMP_similar
    >> metis_tac [code_similar_trans,code_similar_loc_to_pc])
  \\ pairarg_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ qmatch_goalsub_abbrev_tac`_ ∧ all_enc_ok c labs ffis _ (pad_code nop sec_list) ∧ _`
  \\ qmatch_assum_abbrev_tac`enc_secs_again _ labs0 ffis enc code = (code1,T)`
  \\ qpat_x_assum`Abbrev(code1 = _)`kall_tac
  \\ `all_encd0 enc code1` by imp_res_tac enc_secs_again_encd0
  \\ qmatch_assum_abbrev_tac`enc_secs_again _ labs ffis enc code2 = (sec_list,T)`
  \\ `EVERY sec_label_one code2` by metis_tac[upd_lab_len_label_one]
  \\ `all_encd0 enc code2` by metis_tac[upd_lab_len_encd0,enc_secs_again_encd0]
  \\ `all_encd enc labs ffis init_pos sec_list` by metis_tac[enc_secs_again_encd]
  \\ `LENGTH nop ≠ 1 ⇒
      EVERY (sec_aligned (LENGTH nop)) sec_list ∧
      EVERY sec_label_zero sec_list`
  by (
    strip_tac
    \\ qmatch_assum_abbrev_tac`enc_ok c`
    \\ `c.code_alignment ≠ 0`
    by ( strip_tac \\ fs[enc_ok_def] )
    \\ `EVERY sec_ends_with_label code1`
    by metis_tac[enc_secs_again_ends_with_label]
    \\ `EVERY sec_label_zero code2`
    by (
      simp[Abbr`code2`]
      \\ match_mp_tac (GEN_ALL upd_lab_len_encd0_label_zero)
      \\ asm_exists_tac \\ fs[] )
    \\ reverse conj_tac
    >- metis_tac[enc_secs_again_label_zero]
    \\ match_mp_tac enc_secs_again_aligned
    \\ fs[enc_ok_def] \\ rfs[]
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["enc"]))
    \\ qexists_tac`enc` \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ simp[Abbr`nop`]
    \\ match_mp_tac all_encd0_aligned
    \\ fs[enc_ok_def]
    \\ metis_tac[])
  \\ `EVERY sec_label_one sec_list` by metis_tac[enc_secs_again_label_one]
  \\ `all_length_leq sec_list` by metis_tac[all_encd_length_leq]
  \\ `EVERY sec_label_prefix_zero code2`
  by (
    simp[Abbr`code2`]
    \\ match_mp_tac upd_lab_len_label_prefix_zero
    \\ simp[]
    \\ match_mp_tac enc_secs_again_ends_with_label
    \\ asm_exists_tac \\ fs[])
  \\ `EVERY sec_label_prefix_zero sec_list`
  by metis_tac[enc_secs_again_label_prefix_zero]
  \\ `all_lab_len_pos_ok init_pos sec_list`
  by metis_tac[enc_secs_again_pos_ok,upd_lab_len_pos_ok]
  (* all_enc_ok_pre *)
  \\ conj_asm1_tac
  >-
    (match_mp_tac all_enc_ok_pre_pad_code>>
    match_mp_tac enc_secs_again_all_enc_ok_pre>>asm_exists_tac>>
    fs[Abbr`code2`]>>
    match_mp_tac all_enc_ok_pre_upd_lab_len>>
    match_mp_tac enc_secs_again_all_enc_ok_pre>>asm_exists_tac>>fs[])
  (* sec_labels_ok *)
  \\ conj_asm1_tac >-
     metis_tac[enc_secs_again_sec_labels_ok,upd_lab_len_sec_labels_ok,pad_code_sec_labels_ok]
  (* all_enc_ok *)
  \\ conj_asm1_tac
  >- (
    match_mp_tac all_enc_ok_pre_light_imp_all_enc_ok \\ fs[]
    \\ conj_asm1_tac
    >- (
      match_mp_tac all_enc_with_nop_pad_code
      \\ fs[enc_ok_def]
      \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
      \\ simp[] )
    \\ conj_tac
    >- (
      match_mp_tac even_labels_ends_imp_strong
      \\ reverse conj_asm2_tac
      >- metis_tac[enc_secs_again_ends_with_label,upd_lab_len_ends_with_label,
                   pad_code_ends_with_label,all_enc_with_nop_label_zero]
      \\ match_mp_tac label_zero_pos_ok_even_labels \\ fs[]
      \\ match_mp_tac all_lab_len_pos_ok_pad_code \\ fs[])
    \\ conj_tac >- (
      (* TODO: this is slightly weird: zero_labs_acc_exist is moved upwards *)
      fs[zero_labs_acc_exist_eq]>>
      `get_labels (pad_code nop sec_list) = get_labels code` by
        metis_tac[code_similar_pad_code, code_similar_get_labels,
          code_similar_refl, code_similar_upd_lab_len,enc_secs_again_IMP_similar]>>
      fs[]>>
      match_mp_tac enc_secs_again_all_labs_exist
      \\ asm_exists_tac \\ simp[]
      \\ rw[all_labs_exist_get_labels]
      \\ `MAP Section_num code2 = MAP Section_num code`
      by metis_tac[code_similar_MAP_Section_num,
                   enc_secs_again_IMP_similar,
                   code_similar_upd_lab_len]
      \\ qspecl_then[`init_pos`,`code2`,`init_labs`]mp_tac labs_domain_compute_labels_alt
      \\ impl_tac >- metis_tac[]
      \\ simp[] \\ strip_tac \\
      `get_labels code2 = get_labels code ∧ get_code_labels code2 = get_code_labels code`
      by
        (qspecl_then[`code2`,`code1`]mp_tac code_similar_get_code_labels
        \\ impl_tac >- metis_tac[code_similar_upd_lab_len,code_similar_refl]
        \\ rw[] \\ simp[Abbr`code2`]
        \\ metis_tac [enc_secs_again_IMP_similar, code_similar_get_code_labels, code_similar_get_labels])>>
      simp[]>>
      `get_labels code = restrict_zero (get_labels code) ∪ restrict_nonzero (get_labels code)` by
      (fs[EXTENSION,FORALL_PROD,backendPropsTheory.restrict_zero_def,backendPropsTheory.restrict_nonzero_def]>>
      metis_tac[])>>
      pop_assum SUBST1_TAC>>fs[]>>
      metis_tac[SUBSET_TRANS,SUBSET_UNION])
    \\ match_mp_tac offset_ok_pad_code \\ fs[]
    \\ metis_tac[enc_secs_again_offset_ok])
  \\ conj_asm1_tac
  THEN1 (imp_res_tac enc_secs_again_IMP_similar \\
         metis_tac [code_similar_trans,code_similar_sym,code_similar_upd_lab_len,code_similar_pad_code])
  \\ conj_tac THEN1
   (strip_tac
    \\ match_mp_tac has_odd_inst_alignment
    \\ asm_exists_tac \\ srw_tac[][]
    \\ asm_exists_tac \\ srw_tac[][])
  \\ old_drule pad_code_compute_labels
  \\ disch_then(qspecl_then[`init_pos`,`init_labs`]mp_tac)
  \\ impl_tac >- fs[]
  \\ old_drule enc_secs_again_compute_labels \\ fs[]
  \\ rw [Abbr`labs`]
  \\ qhdtm_assum`compute_labels_alt`sym_sub_tac
  THEN1 (
    match_mp_tac all_enc_ok_lab_lookup_even>>
    first_assum (match_exists_tac o concl)>>fs[]>>
    CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac`init_labs`
    \\ asm_exists_tac \\ fs[]
    \\ fs[lab_lookup_def]
    \\ metis_tac[OPTION_ALL_def])
  THEN1 (
    fs[IN_DISJOINT]>>
    first_assum (fn th => mp_tac (SIMP_RULE std_ss [lab_lookup_def] th))>>
    CASE_TAC>> rw[]>>
    fs[domain_lookup]>>
    metis_tac[lab_lookup_compute_labels_alt_ignore,code_similar_MAP_Section_num]
  )
  \\ fs [] \\ match_mp_tac (lab_lookup_compute_labels_test |> GEN_ALL)
  \\ fs[GSYM PULL_EXISTS]
  \\ conj_tac
    >- metis_tac[code_similar_MAP_Section_num,code_similar_pad_code]
  \\ conj_tac >- (
    fs[GSYM ALL_EL_MAP]
    \\ metis_tac[code_similar_extract_labels,code_similar_pad_code] )
  \\ CONJ_TAC >- metis_tac[]
  \\ qpat_x_assum `_ = SOME x2` (fn th => fs [GSYM th])
  \\ match_mp_tac code_similar_loc_to_pc
  \\ match_mp_tac code_similar_sym
  \\ match_mp_tac code_similar_pad_code
  \\ imp_res_tac enc_secs_again_IMP_similar
  \\ fs [code_similar_upd_lab_len,Abbr`code2`]
  \\ metis_tac [code_similar_trans]);
val _=capture "remove_labels_loop_thm" remove_labels_loop_thm;
val _=types "remove_labels_loop_thm_types" remove_labels_loop_thm;
val _=print("hypotheses="^Int.toString(length(hyp remove_labels_loop_thm))^"\n");
val _=show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val template = ``<| ISA := RISC_V; encode := (λa.[0w]); big_endian := F; code_alignment := 0;
 link_reg := SOME 7; avoid_regs := []; reg_count := 8; fp_reg_count := 4;
 two_reg_arith := F; valid_imm := (K (K T));
 addr_offset := (128w,127w); hw_offset := (128w,127w); byte_offset := (128w,127w);
 jump_offset := (128w,127w); cjump_offset := (128w,127w); loc_offset := (128w,127w)
 |> : 8 asm_config``;
val cfg = template;
val _=observe "empty" ``remove_labels_loop 0 ^cfg 18 LN [] [] = SOME ([],LN)``;
val _=observe "retry_zero" ``remove_labels_loop 0 ^cfg 18 LN [] [Section 1 [LabAsm Halt 99w [] 0;Label 1 7 0]] = NONE``;
val _=observe "retry_one" ``OPTION_MAP (λr. lab_lookup 1 7 (SND r)) (remove_labels_loop 1 ^cfg 18 LN [] [Section 1 [LabAsm Halt 99w [] 0;Label 1 7 0]]) = SOME (SOME 20)``;
val _=observe "odd_padding" ``OPTION_MAP (λr. prog_to_bytes (FST r)) (remove_labels_loop 0 ^cfg 18 LN [] [Section 1 [Asm (Asmi (Inst Skip)) [0w] 1;Label 1 7 0]]) = SOME [0w;0w]``;
val _=observe "labels_only" ``OPTION_MAP (λr. lab_lookup 1 7 (SND r)) (remove_labels_loop 0 ^cfg 18 LN [] [Section 1 [Label 1 7 0]]) = SOME (SOME 18)``;
val _=observe "light_reject" ``remove_labels_loop 0 ^cfg 18 LN [] [Section 1 [LabAsm (Call (Lab 1 7)) 0w [0w] 1;Label 1 7 0]] = NONE``;
val cfg1 = ``<| ISA := RISC_V; encode := (λa.[0w]); big_endian := F; code_alignment := 0;
 link_reg := SOME 7; avoid_regs := []; reg_count := 8; fp_reg_count := 4;
 two_reg_arith := F; valid_imm := (K (K T)); addr_offset := (0w,1w); hw_offset := (0w,1w);
 byte_offset := (0w,1w); jump_offset := (0w,1w); cjump_offset := (0w,1w); loc_offset := (0w,1w) |> : 1 asm_config``;
val cfg80 = ``<| ISA := RISC_V; encode := (λa.[0w]); big_endian := F; code_alignment := 0;
 link_reg := SOME 7; avoid_regs := []; reg_count := 8; fp_reg_count := 4;
 two_reg_arith := F; valid_imm := (K (K T)); addr_offset := (128w,127w); hw_offset := (128w,127w);
 byte_offset := (128w,127w); jump_offset := (128w,127w); cjump_offset := (128w,127w); loc_offset := (128w,127w) |> : 80 asm_config``;
val _=observe "width1_large" ``remove_labels_loop 0 ^cfg1 1208925819614629174706176 LN [] [] = SOME ([],LN)``;
val _=observe "width80_large" ``remove_labels_loop 0 ^cfg80 1208925819614629174706176 LN [] [] = SOME ([],LN)``;
