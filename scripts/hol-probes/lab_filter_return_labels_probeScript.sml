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
val next_label_filter_skip = prove (``  ∀code.
  next_label code = next_label (filter_skip code)``,
  ho_match_mp_tac next_label_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[next_label_def,filter_skip_def,not_skip_def]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[next_label_def]);
val th = next_label_filter_skip;
val _ = show_types := true;
val _ = capture "next_label_filter_skip" th;
val _ = types "next_label_filter_skip_types" th;
val _ = print("next_label_filter_skip_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "next_label_filter_skip_proved" th;

(* Unchanged original local statement and proof. *)
val all_skips_get_lab_after = prove (``  ∀code k.
  all_skips 0 code k ⇒
  get_lab_after k code =
  get_lab_after 0 (filter_skip code)``,
  Induct>>full_simp_tac(srw_ss())[get_lab_after_def,filter_skip_def]>>
  Induct>>Induct_on`l`>>srw_tac[][]>>full_simp_tac(srw_ss())[filter_skip_def,get_lab_after_def]
  >-
    (first_assum match_mp_tac>>full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def])
  >>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[is_Label_not_skip]
  >-
    (simp[get_lab_after_def]>>
    first_assum match_mp_tac>>
    full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def])
  >>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]
  >-
    (`not_skip h` by
      (full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]>>
      Cases_on`h`>>fs[not_skip_def]>>
      Cases_on`a`>>fs[]>>
      Cases_on`a'`>>fs[]>>
      Cases_on`i`>>fs[])>>
    full_simp_tac(srw_ss())[get_lab_after_def]>>
    mp_tac next_label_filter_skip>>
    disch_then(qspec_then`Section n l::code` assume_tac)>>
    full_simp_tac(srw_ss())[filter_skip_def])
  >>
    `¬not_skip h` by
      (full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]>>
      first_x_assum(qspec_then`0` mp_tac)>>impl_tac>-
        DECIDE_TAC>>
      srw_tac[][]>>
      full_simp_tac(srw_ss())[not_skip_def])>>
    full_simp_tac(srw_ss())[]>>first_assum match_mp_tac>>
    full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]>>srw_tac[][]>>
    `i+1 < k` by DECIDE_TAC>>
    res_tac>>
    full_simp_tac(srw_ss())[]);
val th = all_skips_get_lab_after;
val _ = show_types := true;
val _ = capture "all_skips_get_lab_after" th;
val _ = types "all_skips_get_lab_after_types" th;
val _ = print("all_skips_get_lab_after_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "all_skips_get_lab_after_proved" th;

(* Unchanged original local statement and proof. *)
val get_lab_after_adjust = prove (``  ∀pc code k.
  all_skips pc code k ⇒
  get_lab_after (pc+k) code = get_lab_after (adjust_pc pc code) (filter_skip code)``,
  ho_match_mp_tac get_lab_after_ind>>
  srw_tac[][]
  >-
    (simp[Once adjust_pc_def,filter_skip_def]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[get_lab_after_def])
  >-
    (full_simp_tac(srw_ss())[filter_skip_def,get_lab_after_def]>>simp[Once adjust_pc_def]>>
    IF_CASES_TAC
    >-
      (full_simp_tac(srw_ss())[Once adjust_pc_def]>>
      first_assum match_mp_tac>>
      full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def])
    >>
      first_assum(qspec_then`k'` mp_tac)>>
      impl_tac>-
        full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]
      >> simp[])
  >>
    Cases_on`is_Label y`>>full_simp_tac(srw_ss())[]
    >-
      (simp[get_lab_after_def,Once adjust_pc_def]>>
      `not_skip y` by
        (Cases_on`y`>>full_simp_tac(srw_ss())[is_Label_def,not_skip_def])>>
      full_simp_tac(srw_ss())[filter_skip_def,get_lab_after_def]>>
      IF_CASES_TAC
      >-
        (full_simp_tac(srw_ss())[Once adjust_pc_def]>>
        first_assum match_mp_tac>>
        full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def])
      >>
        first_assum(qspec_then`k'` mp_tac)>>
        impl_tac>-
          full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]>>
        simp[])
    >>
      simp[Once adjust_pc_def]>>IF_CASES_TAC>>full_simp_tac(srw_ss())[]
      >-
        metis_tac[all_skips_get_lab_after]
      >>
      full_simp_tac(srw_ss())[get_lab_after_def]>>
      IF_CASES_TAC>>
      full_simp_tac(srw_ss())[filter_skip_def,get_lab_after_def]>>
      `∀x. x + pc -1 = pc -1 + x` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[]>>
      first_assum match_mp_tac>>
      `∀x. pc + x -1 = pc -1 +x` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]);
val th = get_lab_after_adjust;
val _ = show_types := true;
val _ = capture "get_lab_after_adjust" th;
val _ = types "get_lab_after_adjust_types" th;
val _ = print("get_lab_after_adjust_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "get_lab_after_adjust_proved" th;
