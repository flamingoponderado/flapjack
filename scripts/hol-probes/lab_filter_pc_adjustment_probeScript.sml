load "bossLib";
load "preamble";
load "lab_filterProofTheory";
open bossLib HolKernel Parse preamble labSemTheory lab_filterTheory lab_filterProofTheory;
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

val adjust_pc_all_skips = prove (``  ∀k pc code.
  all_skips pc code k ⇒
  adjust_pc pc code +1 = adjust_pc (pc+k+1) code``,
  Induct>>full_simp_tac(srw_ss())[all_skips_def]>>simp[]>>
  ho_match_mp_tac asm_fetch_aux_ind
  >>
  full_simp_tac(srw_ss())[asm_fetch_aux_def]>>srw_tac[][]>>simp[Once adjust_pc_def,SimpRHS]>>
  simp[Once adjust_pc_def]>>
  TRY (IF_CASES_TAC>>full_simp_tac(srw_ss())[not_skip_def]>>
      full_simp_tac(srw_ss())[Once adjust_pc_def]>>
      pop_assum mp_tac >> EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>NO_TAC)
  >-
    (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    `pc - 1 + 1 = pc` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[])
  >-
    (pop_assum(qspec_then`k` mp_tac)>>full_simp_tac(srw_ss())[])
  >>
    full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>Cases_on`pc=0`
    >-
      (first_assum(qspec_then`0` mp_tac)>>
      full_simp_tac(srw_ss())[]>>impl_tac>-DECIDE_TAC>>strip_tac>>
      full_simp_tac(srw_ss())[not_skip_def]>>
      first_x_assum(qspecl_then[`0`,`Section k' ys::xs`]mp_tac)>>impl_tac>-
      (full_simp_tac(srw_ss())[]>>srw_tac[][]>>
      first_x_assum(qspec_then`i+1` mp_tac)>>impl_tac>-DECIDE_TAC>>
      srw_tac[][])>>
      full_simp_tac(srw_ss())[Once adjust_pc_def])
    >>
    full_simp_tac(srw_ss())[]>>IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    `pc -1 + (k+1 +1) = pc +(k+1)` by DECIDE_TAC>>
    `pc -1 + (k+1) = pc + k` by DECIDE_TAC>>
    `pc  + (k+1) -1 = pc + k` by DECIDE_TAC>>
    `!i. i+(pc-1) = i+pc -1` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[]>>
    first_assum match_mp_tac>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[]);
val th = adjust_pc_all_skips;
val _ = show_types := true;
val _ = capture "adjust_pc_all_skips" th;
val _ = types "adjust_pc_all_skips_types" th;
val _ = print("adjust_pc_all_skips_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "adjust_pc_all_skips_proved" th;
val all_skips_initial_adjust = prove (``  ∀code.
  ∃k. all_skips 0 code k ∧ adjust_pc k code = 0``,
  Induct>>full_simp_tac(srw_ss())[all_skips_def]
  >-
    (qexists_tac`0`>>full_simp_tac(srw_ss())[adjust_pc_def,asm_fetch_aux_def])
  >>
  Induct>>Induct_on`l`>>srw_tac[][]
  >-
    (simp[Once adjust_pc_def]>>
    qexists_tac`k`>>full_simp_tac(srw_ss())[asm_fetch_aux_def])
  >>
    pop_assum(qspec_then`n` assume_tac)>>full_simp_tac(srw_ss())[]>>
    Cases_on`h`>>
    simp[Once adjust_pc_def,asm_fetch_aux_def,is_Label_def,not_skip_def]
    >-
      (qexists_tac`k'`>>full_simp_tac(srw_ss())[])
    >-
      (Cases_on`a=Asmi(Inst Skip)`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`k'+1`>>srw_tac[][]>>
        `i-1 < k'` by DECIDE_TAC>>
        metis_tac[])
      >> (qexists_tac`0`>>full_simp_tac(srw_ss())[]))
    >> (qexists_tac`0`>>full_simp_tac(srw_ss())[]));
val th = all_skips_initial_adjust;
val _ = show_types := true;
val _ = capture "all_skips_initial_adjust" th;
val _ = types "all_skips_initial_adjust_types" th;
val _ = print("all_skips_initial_adjust_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "all_skips_initial_adjust_proved" th;
