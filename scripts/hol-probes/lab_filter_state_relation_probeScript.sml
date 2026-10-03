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

val asm_fetch_not_skip_adjust_pc = prove (``  ∀pc code inst.
  (∀x y.asm_fetch_aux pc code ≠ SOME (Asm (Asmi(Inst Skip)) x y)) ⇒
  asm_fetch_aux pc code = asm_fetch_aux (adjust_pc pc code) (filter_skip code)``,
  ho_match_mp_tac asm_fetch_aux_ind>>srw_tac[][]
  >-
    simp[asm_fetch_aux_def,filter_skip_def]
  >-
    (full_simp_tac(srw_ss())[asm_fetch_aux_def,filter_skip_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    IF_CASES_TAC>>
    metis_tac[adjust_pc_def])
  >>
  Cases_on`is_Label y`>>full_simp_tac(srw_ss())[]
  >-
    (full_simp_tac(srw_ss())[asm_fetch_aux_def,filter_skip_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    simp[is_Label_not_skip]>>
    IF_CASES_TAC>>
    res_tac>>full_simp_tac(srw_ss())[]>>
    simp[asm_fetch_aux_def]>>
    simp[Once adjust_pc_def])
  >>
  reverse(Cases_on`pc ≠ 0`>>full_simp_tac(srw_ss())[])
  >-
    (full_simp_tac(srw_ss())[asm_fetch_aux_def,Once adjust_pc_def,filter_skip_def,not_skip_def]>>
    EVERY_CASE_TAC>>
    full_simp_tac(srw_ss())[asm_fetch_aux_def,is_Label_def])
  >>
    full_simp_tac(srw_ss())[Once asm_fetch_aux_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[filter_skip_def]>>
    simp[asm_fetch_aux_def]);
val th = asm_fetch_not_skip_adjust_pc;
val _ = show_types := true;
val _ = capture "asm_fetch_not_skip_adjust_pc" th;
val _ = types "asm_fetch_not_skip_adjust_pc_types" th;
val _ = print("asm_fetch_not_skip_adjust_pc_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "asm_fetch_not_skip_adjust_pc_proved" th;
val th = DB.fetch "lab_filterProof" "state_rel_def";
val _ = show_types := true;
val _ = capture "state_rel_def" th;
val _ = types "state_rel_def_types" th;
val _ = print("state_rel_def_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "state_rel_def_proved" th;
val asm_fetch_aux_eq2 = prove (``  asm_fetch_aux (adjust_pc pc code) (filter_skip code) = x ⇒
  ∃k.
  asm_fetch_aux (pc+k) code = x ∧
  all_skips pc code k``,
  metis_tac[asm_fetch_aux_eq]);
val th = asm_fetch_aux_eq2;
val _ = show_types := true;
val _ = capture "asm_fetch_aux_eq2" th;
val _ = types "asm_fetch_aux_eq2_types" th;
val _ = print("asm_fetch_aux_eq2_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "asm_fetch_aux_eq2_proved" th;
val all_skips_evaluate_0 = all_skips_evaluate |>SIMP_RULE std_ss [PULL_FORALL]|>(Q.SPECL[`k`,`s`,`0`])|>GEN_ALL|>SIMP_RULE std_ss[];
val all_skips_evaluate_rw = prove (``  all_skips s.pc s.code k ∧ ¬s.failed ∧
  s.clock = clk + k ∧
  t = s with <| pc:= s.pc +k ; clock := clk |> ⇒
  evaluate s = evaluate t``,
  srw_tac[][]>>
  qabbrev_tac`s' = s with clock := clk`>>
  `s = s' with clock := s'.clock +k` by
    full_simp_tac(srw_ss())[Abbr`s'`,state_component_equality]>>
  `s' with pc := s.pc +k =
   s' with <| pc := s'.pc +k ; clock := s'.clock|>` by full_simp_tac(srw_ss())[state_component_equality]>>
   ntac 2 (pop_assum SUBST_ALL_TAC)>>
   match_mp_tac all_skips_evaluate_0>>
   full_simp_tac(srw_ss())[state_component_equality]);
val th = all_skips_evaluate_rw;
val _ = show_types := true;
val _ = capture "all_skips_evaluate_rw" th;
val _ = types "all_skips_evaluate_rw_types" th;
val _ = print("all_skips_evaluate_rw_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "all_skips_evaluate_rw_proved" th;
