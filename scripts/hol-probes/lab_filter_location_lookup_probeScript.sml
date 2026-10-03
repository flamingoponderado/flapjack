load "bossLib";
load "preamble";
load "lab_filterProofTheory";
open bossLib HolKernel Parse preamble labSemTheory lab_filterTheory lab_filterProofTheory;
(* Exact temporary simplifier setup from original script lines10/12. *)
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];
val _ = temp_delsimps ["NORMEQ_CONV"];
fun capture label th = (print(label ^ "=");print_term(concl th);print "\n");
fun types label th = (print(label ^ "=");app(fn v=>print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))(fst(strip_forall(concl th)) @ free_vars(concl th));print "\n");
fun checked label th = (print(label ^ "="); print_term(rhs(concl(EQT_INTRO (prove(concl th,ACCEPT_TAC th)))));print "\n");
(* Non-exported local theorem: unchanged original statement and proof. *)
val is_Label_not_skip = prove (``  is_Label y ⇒ not_skip y``,
  Cases_on`y`>>full_simp_tac(srw_ss())[is_Label_def,not_skip_def]);
(* Non-exported local theorem: unchanged original statement and proof. *)
val state_rw = prove (``  s with clock := s.clock = s ∧
  s with pc := s.pc = s ∧
  s with <|pc := s.pc; clock:= s.clock+k'|> = s with clock:=s.clock+k'``,
  full_simp_tac(srw_ss())[state_component_equality]);
(* Non-exported local theorem: unchanged original statement and proof. *)
val all_skips_evaluate = prove (``  ∀k s.
  all_skips s.pc s.code k ∧
  ¬s.failed ⇒
  ∀k'.
  evaluate (s with clock:= s.clock +k' + k) =
  evaluate (s with <|pc := s.pc +k; clock:= s.clock +k'|>)``,
  Induct>>full_simp_tac(srw_ss())[all_skips_def]
  >-
    metis_tac[state_rw]
  >>
    srw_tac[][]>>first_assum(qspec_then`0` mp_tac)>>
    impl_tac>-
      full_simp_tac(srw_ss())[]>>
    strip_tac>>full_simp_tac(srw_ss())[]>>
    simp[Once evaluate_def,asm_fetch_def,asm_inst_def]>>
    full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def]>>
    full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
    `k' + (k+1 + s.clock) -1 = k' + s.clock+k` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[]>>
    first_x_assum(qspec_then `s with <|pc:=s.pc+1;clock:=k'+s.clock|>` mp_tac)>>
    impl_tac>-
      (srw_tac[][]>>first_x_assum(qspec_then`i+1` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
      metis_tac[arithmeticTheory.ADD_COMM,ADD_ASSOC])>>
    srw_tac[][]>>first_x_assum(qspec_then`0` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    metis_tac[arithmeticTheory.ADD_COMM,ADD_ASSOC]);

(* Unchanged original local statement and proof. *)
val loc_to_pc_eq_NONE = prove (``  ∀n1 n2 code.
  loc_to_pc n1 n2 (filter_skip code) = NONE ⇒
  loc_to_pc n1 n2 code = NONE``,
  ho_match_mp_tac loc_to_pc_ind>>
  rw[]>>gvs[filter_skip_def]>>
  simp[Once loc_to_pc_def]>>
  pop_assum mp_tac>>
  simp[Once loc_to_pc_def]>>
  qmatch_goalsub_abbrev_tac`P ∧ _ = _`>>
  strip_tac>>
  qpat_x_assum`Abbrev _` mp_tac>>
  gvs[]>>
  TOP_CASE_TAC>>gvs[]>>
  strip_tac>>
  CONJ_ASM1_TAC
  >- (
    gvs[AllCaseEqs()]>>
    fs[not_skip_def,AllCasePreds()])>>
  rename1`P ∧ _ ⇒ _`>>
  gvs[]>>
  qpat_x_assum`_ = NONE` mp_tac>>
  IF_CASES_TAC>>simp[]
  >-
    (IF_CASES_TAC>>gvs[AllCaseEqs()])>>
  `¬is_Label h` by (
    Cases_on`h`>>
    gvs[not_skip_def,AllCasePreds()])>>
  gvs[AllCaseEqs()]>>
  rw[]>>
  first_x_assum irule>>
  simp[Once loc_to_pc_def]);
val th = loc_to_pc_eq_NONE;
val _ = show_types := true;
val _ = capture "loc_to_pc_eq_NONE" th;
val _ = types "loc_to_pc_eq_NONE_types" th;
val _ = print("loc_to_pc_eq_NONE_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "loc_to_pc_eq_NONE_proved" th;
(* Unchanged original local statement and proof. *)
val loc_to_pc_eq_SOME = prove (``  ∀n1 n2 code pc.
  loc_to_pc n1 n2 (filter_skip code) = SOME pc ⇒
  ∃pc'.
  loc_to_pc n1 n2 code = SOME pc' ∧
  adjust_pc pc' code = pc``,
  ho_match_mp_tac loc_to_pc_ind>>srw_tac[][]
  >-
    (full_simp_tac(srw_ss())[filter_skip_def,adjust_pc_def]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[])
  >>
  full_simp_tac(srw_ss())[Once loc_to_pc_def]>>IF_CASES_TAC>>full_simp_tac(srw_ss())[]
  >-
    (full_simp_tac(srw_ss())[filter_skip_def,Once loc_to_pc_def]>>
    full_simp_tac(srw_ss())[Once adjust_pc_def])
  >>
    (FULL_CASE_TAC>>full_simp_tac(srw_ss())[filter_skip_def,Once loc_to_pc_def]>>rev_full_simp_tac(srw_ss())[]
    >-
      (full_simp_tac(srw_ss())[Once adjust_pc_def]>>
      IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      simp[Once adjust_pc_def])
    >>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]
    >-
      (full_simp_tac(srw_ss())[not_skip_def]>>
      qpat_x_assum`_=pc` sym_sub_tac>>
      full_simp_tac(srw_ss())[Once adjust_pc_def])
    >>
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]
      >-
        (Cases_on`not_skip h`>>qpat_x_assum`_=SOME pc` mp_tac>>
        TRY(`not_skip h` by (full_simp_tac(srw_ss())[]>>NO_TAC)>>
          simp[Once loc_to_pc_def,SimpLHS])>>
        srw_tac[][]>>
        (last_x_assum(qspec_then`pc` mp_tac)>>
        impl_tac>-
          (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
          DECIDE_TAC)>>
        srw_tac[][]>>
        simp[Once loc_to_pc_def]>>
        simp[Once adjust_pc_def]>>IF_CASES_TAC>>
        full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[Once adjust_pc_def]))
      >>
      Cases_on`not_skip h`>>qpat_x_assum`_=SOME pc` mp_tac
      >-
        (simp[]>>simp[Once loc_to_pc_def,SimpLHS]>>
        srw_tac[][]>>
        last_x_assum(qspec_then`pc-1` mp_tac)>>
        impl_tac>-
          (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
          DECIDE_TAC)>>
        srw_tac[][]>>
        simp[Once loc_to_pc_def]>>
        `pc ≠ 0` by
          (qpat_x_assum`_=SOME pc` mp_tac>>
          EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
          srw_tac[][]>>
          DECIDE_TAC)>>
        simp[Once adjust_pc_def]>>DECIDE_TAC)
      >>
        simp[]>>srw_tac[][]>>
        last_x_assum (qspec_then`pc` mp_tac)>>
        impl_tac>-
         (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
          DECIDE_TAC)>>
        srw_tac[][]>>
        simp[Once loc_to_pc_def]>>
        simp[Once adjust_pc_def])));
val th = loc_to_pc_eq_SOME;
val _ = show_types := true;
val _ = capture "loc_to_pc_eq_SOME" th;
val _ = types "loc_to_pc_eq_SOME_types" th;
val _ = print("loc_to_pc_eq_SOME_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "loc_to_pc_eq_SOME_proved" th;
(* Unchanged original local statement and proof. *)
val loc_to_pc_adjust_pc_append = prove (``  ∀n1 n2 code pc ls.
  loc_to_pc n1 n2 code = SOME pc ==>
  adjust_pc pc code = adjust_pc pc (code++ls)``,
  ho_match_mp_tac loc_to_pc_ind>>rw[]>>
  pop_assum mp_tac>>
  simp[Once loc_to_pc_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (rw[Once adjust_pc_def]>>
    rw[Once adjust_pc_def])>>
  (TOP_CASE_TAC>>fs[]
  >-
    (simp[Once adjust_pc_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    metis_tac[]))>>
  (IF_CASES_TAC>>fs[]
  >-
    (simp[Once adjust_pc_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    metis_tac[]))>>
  (IF_CASES_TAC>>fs[]
  >-
    (simp[Once adjust_pc_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    metis_tac[]))>>
  TOP_CASE_TAC>>
  fs[]>>
  simp[Once adjust_pc_def]>>
  simp[Once adjust_pc_def,SimpRHS]>>
  IF_CASES_TAC>>rw[]>>simp[]);
val th = loc_to_pc_adjust_pc_append;
val _ = show_types := true;
val _ = capture "loc_to_pc_adjust_pc_append" th;
val _ = types "loc_to_pc_adjust_pc_append_types" th;
val _ = print("loc_to_pc_adjust_pc_append_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "loc_to_pc_adjust_pc_append_proved" th;
