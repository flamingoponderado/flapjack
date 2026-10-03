load "bossLib"; load "preamble"; load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory ffiTheory wordSemTheory labSemTheory labPropsTheory lab_to_targetTheory lab_filterProofTheory asmTheory asmSemTheory asmPropsTheory targetSemTheory targetPropsTheory lab_filterTheory semanticsPropsTheory;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = set_trace "BasicProvers.var_eq_old" 1;
val all_enc_ok_pre_filter_skip = prove (``∀code c. all_enc_ok_pre c code ⇒ all_enc_ok_pre c (filter_skip code)``,
Induct>>TRY(Cases)>>fs[lab_filterTheory.filter_skip_def]>>rw[]>> Induct_on`l`>>fs[]>>rw[]);
val semantics_compile_lemma_prime = prove (``
  mc_conf_ok mc_conf ∧
  (no_share_mem_inst code ==>
    compiler_oracle_ok coracle c'.labels (LENGTH bytes) (asm_conf:'a asm_config) mc_conf.ffi_names) ∧
  (* Assumptions on input code *)
  good_code mc_conf.target.config LN code ∧
  (* Config state *)
  asm_conf = mc_conf.target.config /\
  c.labels = LN ∧ c.pos = 0 ∧
  lab_to_target$compile asm_conf (c:lab_to_target$config) code = SOME (bytes,c') /\
  (* FFI is either given or computed *)
  c'.ffi_names = SOME mc_conf.ffi_names /\
  good_init_state mc_conf ms bytes cbspace t m dm sdm /\
  (* set up mmio_info and ffi_entry_pcs for mmio *)
  MAP (\rec. w2n (mc_conf.target.get_pc ms) + rec.entry_pc) c'.shmem_extra =
    DROP i (MAP w2n mc_conf.ffi_entry_pcs) /\
  mc_conf.mmio_info = ZIP (GENLIST (λindex. index + i) (LENGTH c'.shmem_extra),
                            (MAP (\rec. (rec.nbytes, Addr rec.addr_reg (n2w rec.addr_off),
                              rec.reg, n2w rec.exit_pc + mc_conf.target.get_pc ms))
                                 c'.shmem_extra)) /\
  no_install_or_no_share_mem code mc_conf.ffi_names /\
  (mmio_pcs_min_index mc_conf.ffi_names = SOME i) /\
  (* to avoid the ffi_entry_pc wraps around and overlaps with the program or code buffer *)
  cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a) /\
  (* the original ffi names provided does not contain MappedRead or MappedWrite *)
  (!ffis. c.ffi_names = SOME ffis ==> EVERY (λx. ∃s. x = ExtCall s) ffis) /\
  semantics (make_init mc_conf ffi t m dm sdm ms code
    (lab_to_target$compile asm_conf) (mc_conf.target.get_pc ms+n2w(LENGTH bytes)) cbspace
    coracle
  ) <> Fail ==>
  machine_sem mc_conf ffi ms =
  {semantics (make_init mc_conf ffi t m dm sdm ms code
    (lab_to_target$compile asm_conf) (mc_conf.target.get_pc ms+n2w(LENGTH bytes)) cbspace
    coracle
  )}``,
  fs[compile_def,compile_lab_def]>>
  pairarg_tac \\ fs[] \\
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  rw[]>>
  `compile mc_conf.target.config =
    (λc p. compile_lab mc_conf.target.config c (filter_skip p)) ` by
    fs[FUN_EQ_THM,compile_def]>>
  pop_assum SUBST_ALL_TAC>>
  gvs[] >>
  fs[GSYM make_init_filter_skip]>>
  SIMP_TAC (bool_ss) [Once WORD_ADD_COMM]>>
  qabbrev_tac `info=get_shmem_info q 0 [] []` >>
  first_x_assum $ mp_tac o GSYM o ONCE_REWRITE_RULE[markerTheory.Abbrev_def] >>
  pairarg_tac >>
  strip_tac >>
  gvs[ELIM_UNCURRY] >>
  match_mp_tac (GEN_ALL $ SRULE[] semantics_make_init)>>
  fs[sec_ends_with_label_filter_skip,all_enc_ok_pre_filter_skip]>>
  fs[find_ffi_names_filter_skip,GSYM PULL_EXISTS,MAP_MAP_o,o_DEF]>>
  qpat_x_assum `_ ++ _ = mc_conf.ffi_names` $ assume_tac o GSYM >>
  conj_tac >- fs[mc_conf_ok_def] >>
  conj_tac >- (
    fs[good_code_def] >>
    fs[sec_ends_with_label_filter_skip,all_enc_ok_pre_filter_skip]>>
    fs[GSYM ALL_EL_MAP])>>
  rename1`_ = SOME (q,r)` >>
  qexists `r` >>
  fs[good_init_state_def] >>
  conj_tac >- (
    rpt strip_tac >>
    fs[compiler_oracle_ok_def,no_share_mem_filter_skip] >>
    rw[] >>
    rename1 `coracle k` >>
    last_x_assum(qspec_then`k` assume_tac)>>rfs[]>>
    pairarg_tac \\ fs[] \\
    pairarg_tac \\ fs[] \\ rw[] \\
    fs[good_code_def]>>
    fs[sec_ends_with_label_filter_skip,all_enc_ok_pre_filter_skip]>>
    fs[GSYM ALL_EL_MAP]
  )>>
  qmatch_asmsub_rename_tac `mmio_pcs_min_index (ffis ++ rest) = SOME i` >>
  `mmio_pcs_min_index (ffis ++ rest) = SOME (LENGTH ffis)` by (
    Cases_on`c.ffi_names`
    >- (
      gvs[] >>
      old_drule get_shmem_info_MappedRead_or_MappedWrite >>
      simp[Sh_not_Ext] >>
      strip_tac >>
      old_drule $ GEN_ALL mmio_pcs_min_index_APPEND_thm >>
      qmatch_assum_abbrev_tac`mmio_pcs_min_index (ffi' ++ _) = SOME _` >>
      disch_then $ qspec_then ‘ffi'’ mp_tac>>impl_tac >-
       (irule find_ffi_names_EVERY>>
        gvs[Abbr`ffi'`]>>metis_tac[])>>
      strip_tac>>fs[]
    ) >>
      gvs[] >>
      old_drule get_shmem_info_MappedRead_or_MappedWrite >>
      simp[Sh_not_Ext] >>
      strip_tac >>
      old_drule $ GEN_ALL mmio_pcs_min_index_APPEND_thm >>
      disch_then $ qspec_then ‘ffis’ mp_tac>>fs[]
  ) >>
  gvs[] >>
  conj_tac >- (
    gvs[TAKE_LENGTH_APPEND] >>
    Cases_on `c.ffi_names` >- (
      mp_tac find_ffi_names_EVERY>>
      disch_then $ qspec_then ‘code’ mp_tac>>
      simp[GSYM FILTER_EQ_ID]>>strip_tac>>fs[list_subset_refl])>>
    gvs[list_subset_TAKE,list_subset_refl]>>
    irule list_subset_trans>>
    last_assum $ irule_at Any>>
    mp_tac find_ffi_names_EVERY>>
    simp[GSYM FILTER_EQ_ID]>>
    strip_tac>>fs[list_subset_refl]
  ) >>
  conj_tac >- (
    qexists `c.init_clock` >>
    gvs[TAKE_LENGTH_APPEND]
  ) >>
  simp[DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
  simp[GSYM word_add_n2w, n2w_w2n]>>
  simp[no_install_or_no_share_mem_filter_skip] >>
  gvs[start_pc_ok_def,MEM_EL]>>
  rw[] >>
  spose_not_then assume_tac >>
  gvs[] >>
  last_x_assum $ drule_then assume_tac >>
  rw[]>>
  gvs[find_index_LEAST_EL] >>
  qpat_x_assum `(LEAST n'. _) = n` mp_tac >>
  DEEP_INTRO_TAC WhileTheory.LEAST_ELIM >>
  conj_tac
  >- (fs[MEM_EL] >> metis_tac[]) >>
  simp[] >>
  strip_tac >>
  spose_not_then kall_tac >>
  first_x_assum $ assume_tac o GSYM >>
  gvs[addressTheory.word_arith_lemma1,EL_TAKE] >>
  qpat_x_assum `n2w _ = -n2w _ ` $ assume_tac >>
  old_drule $ iffLR o GSYM $ cj 1 addressTheory.WORD_EQ_ADD_CANCEL >>
  disch_then $ qspec_then `n2w (ffi_offset * (n + 3))` mp_tac >>
  first_x_assum kall_tac >>
  PURE_REWRITE_TAC[cj 1 addressTheory.word_arith_lemma1,WORD_LITERAL_ADD,WORD_ADD_COMM] >>
  simp[] >>
  `cbspace + (LENGTH (prog_to_bytes q) + ffi_offset * (n + 3)) < dimword (:'a)`
    by (
      drule_at_then Any irule LESS_TRANS >>
      simp[ADD_COMM,ffi_offset_def]
  ) >>
  `bn  + (LENGTH (prog_to_bytes q) + ffi_offset * (n + 3)) < dimword (:'a)`
    by (
      drule_at_then (Pos $ el 2) irule LESS_TRANS >>
      simp[LESS_MONO_ADD]
  ) >>
  gvs[ffi_offset_def]);
val semantics_compile_lemma = semantics_compile_lemma_prime |> REWRITE_RULE [CONJ_ASSOC] |> MATCH_MP implements_intro_gen |> REWRITE_RULE [GSYM CONJ_ASSOC];
val th = semantics_compile_lemma_prime;
val _ = show_types := true;
val _ = print "semantics_compile_lemma_prime=";
val _ = print_term (concl th);
val _ = print "\n";
val _ = print "semantics_compile_lemma_prime_types=";
val _ = app (fn v => print (term_to_string v ^ ":" ^ type_to_string (type_of v) ^ ";")) (fst (strip_forall (concl th)) @ free_vars (concl th));
val _ = print "\n";
val _ = print ("semantics_compile_lemma_prime_hypotheses=" ^ Int.toString (length (hyp th)) ^ "\n");
val _ = show_types := false;
val _ = print "semantics_compile_lemma_prime_proved=";
val _ = print_term (rhs (concl (EQT_INTRO (prove (concl th, ACCEPT_TAC th)))));
val _ = print "\n";
val th = semantics_compile_lemma;
val _ = show_types := true;
val _ = print "semantics_compile_lemma=";
val _ = print_term (concl th);
val _ = print "\n";
val _ = print "semantics_compile_lemma_types=";
val _ = app (fn v => print (term_to_string v ^ ":" ^ type_to_string (type_of v) ^ ";")) (fst (strip_forall (concl th)) @ free_vars (concl th));
val _ = print "\n";
val _ = print ("semantics_compile_lemma_hypotheses=" ^ Int.toString (length (hyp th)) ^ "\n");
val _ = show_types := false;
val _ = print "semantics_compile_lemma_proved=";
val _ = print_term (rhs (concl (EQT_INTRO (prove (concl th, ACCEPT_TAC th)))));
val _ = print "\n";
