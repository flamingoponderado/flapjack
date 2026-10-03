load "bossLib";
load "preamble";
load "lab_filterProofTheory";
open bossLib HolKernel Parse preamble labSemTheory lab_filterTheory lab_filterProofTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "=");print_term(concl th);print "\n");
fun types label th = (print(label ^ "=");app(fn v=>print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))(fst(strip_forall(concl th)) @ free_vars(concl th));print "\n");
fun checked label th = (print(label ^ "="); print_term(rhs(concl(EQT_INTRO (prove(concl th,ACCEPT_TAC th)))));print "\n");
val th = DB.fetch "lab_filterProof" "adjust_pc_def";
val _ = show_types := true;
val _ = capture "adjust_pc_def" th;
val _ = types "adjust_pc_def_types" th;
val _ = print("adjust_pc_def_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "adjust_pc_def_proved" th;
val th = DB.fetch "lab_filterProof" "all_skips_def";
val _ = show_types := true;
val _ = capture "all_skips_def" th;
val _ = types "all_skips_def_types" th;
val _ = print("all_skips_def_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "all_skips_def_proved" th;
(* Non-exported local theorem: unchanged original statement and proof. *)
val is_Label_not_skip = prove (``  is_Label y ⇒ not_skip y``,
  Cases_on`y`>>full_simp_tac(srw_ss())[is_Label_def,not_skip_def]);
val th = is_Label_not_skip;
val _ = show_types := true;
val _ = capture "is_Label_not_skip" th;
val _ = types "is_Label_not_skip_types" th;
val _ = print("is_Label_not_skip_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "is_Label_not_skip_proved" th;
val th = DB.fetch "lab_filterProof" "asm_fetch_aux_eq";
val _ = show_types := true;
val _ = capture "asm_fetch_aux_eq" th;
val _ = types "asm_fetch_aux_eq_types" th;
val _ = print("asm_fetch_aux_eq_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "asm_fetch_aux_eq_proved" th;
(* Non-exported local theorem: unchanged original statement and proof. *)
val state_rw = prove (``  s with clock := s.clock = s ∧
  s with pc := s.pc = s ∧
  s with <|pc := s.pc; clock:= s.clock+k'|> = s with clock:=s.clock+k'``,
  full_simp_tac(srw_ss())[state_component_equality]);
val th = state_rw;
val _ = show_types := true;
val _ = capture "state_rw" th;
val _ = types "state_rw_types" th;
val _ = print("state_rw_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "state_rw_proved" th;
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
val th = all_skips_evaluate;
val _ = show_types := true;
val _ = capture "all_skips_evaluate" th;
val _ = types "all_skips_evaluate_types" th;
val _ = print("all_skips_evaluate_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val _ = show_types := false;
val _ = checked "all_skips_evaluate_proved" th;
