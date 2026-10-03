load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val full = DB.fetch "lab_to_targetProof" "IMP_state_rel_make_init";
val _ = capture "IMP_state_rel_make_init" full;
val _ = types "IMP_state_rel_make_init_types" full;
val _ = print("IMP_state_rel_make_init_hypotheses=" ^ Int.toString(length(hyp full)) ^ "\n");
val guard = lhand(concl full);
val clauses = CONJUNCTS (REWRITE_RULE [state_rel_def] (UNDISCH full));
val _ = print("state_rel_conjuncts=" ^ Int.toString(length clauses) ^ "\n");
fun checked label th = (print(label ^ "="); print_term(rhs(concl(EQT_INTRO (prove(concl th, ACCEPT_TAC th))))); print "\n");
val ISR4 = DISCH guard (List.nth(clauses,18));
val _ = capture "ISR4_statement" ISR4;
val _ = print("ISR4_hypotheses=" ^ Int.toString(length(hyp ISR4)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR4_proved" ISR4;
val _ = show_types := true;
val ISR5 = DISCH guard (List.nth(clauses,19));
val _ = capture "ISR5_statement" ISR5;
val _ = print("ISR5_hypotheses=" ^ Int.toString(length(hyp ISR5)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR5_proved" ISR5;
val _ = show_types := true;
val ISR6 = DISCH guard (List.nth(clauses,21));
val _ = capture "ISR6_statement" ISR6;
val _ = print("ISR6_hypotheses=" ^ Int.toString(length(hyp ISR6)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR6_proved" ISR6;
val _ = show_types := true;
val ISR7 = DISCH guard (List.nth(clauses,22));
val _ = capture "ISR7_statement" ISR7;
val _ = print("ISR7_hypotheses=" ^ Int.toString(length(hyp ISR7)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR7_proved" ISR7;
val _ = show_types := true;
val ISR9 = DISCH guard (List.nth(clauses,30));
val _ = capture "ISR9_statement" ISR9;
val _ = print("ISR9_hypotheses=" ^ Int.toString(length(hyp ISR9)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR9_proved" ISR9;
val _ = show_types := true;
val ISR10 = DISCH guard (List.nth(clauses,31));
val _ = capture "ISR10_statement" ISR10;
val _ = print("ISR10_hypotheses=" ^ Int.toString(length(hyp ISR10)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR10_proved" ISR10;
val _ = show_types := true;
val ISR11 = DISCH guard (List.nth(clauses,34));
val _ = capture "ISR11_statement" ISR11;
val _ = print("ISR11_hypotheses=" ^ Int.toString(length(hyp ISR11)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR11_proved" ISR11;
val _ = show_types := true;
val ISR13 = DISCH guard (List.nth(clauses,40));
val _ = capture "ISR13_statement" ISR13;
val _ = print("ISR13_hypotheses=" ^ Int.toString(length(hyp ISR13)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR13_proved" ISR13;
val _ = show_types := true;
val ISR14 = DISCH guard (List.nth(clauses,47));
val _ = capture "ISR14_statement" ISR14;
val _ = print("ISR14_hypotheses=" ^ Int.toString(length(hyp ISR14)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR14_proved" ISR14;
val _ = show_types := true;
val ISR17 = DISCH guard (List.nth(clauses,52));
val _ = capture "ISR17_statement" ISR17;
val _ = print("ISR17_hypotheses=" ^ Int.toString(length(hyp ISR17)) ^ "\n");
val _ = show_types := false;
val _ = checked "ISR17_proved" ISR17;
val _ = show_types := true;

(* Literal original proof prefix exposes the actual Suspend case clauses.
These goal captures are proof-state observations, not separate theorems. *)
load "proofManagerLib";
open proofManagerLib lab_to_targetTheory targetSemTheory labSemTheory labPropsTheory;
val _ = proofManagerLib.chatting := false;
val _ = set_goal ([],concl full);
val _ = e (
rw[] \\ old_drule $ GEN_ALL remove_labels_thm
  \\ impl_tac >- (
    fs[good_code_def,mc_conf_ok_def]
    \\ rw[lab_lookup_def]>>
    TOP_CASE_TAC>>fs[lookup_def])
  \\ qabbrev_tac `new_shmem_info=MAP (\rec. rec with
      <|entry_pc:=w2n (mc_conf.target.get_pc ms) + rec.entry_pc
       ;exit_pc:=w2n (mc_conf.target.get_pc ms) + rec.exit_pc|>) shmem_info`
  \\ rw[]
  \\ fs[state_rel_def,
        word_loc_val_def,
        make_init_def,
        good_init_state_def,
        mc_conf_ok_def,
        compiler_oracle_ok_def,
        target_configured_def,
        good_code_def,
        start_pc_ok_def]
  \\ rfs[]);
val (_,goal) = hd(top_goals());
val cases = strip_conj goal;
val _ = print("original_residual_cases=" ^ Int.toString(length cases) ^ "\n");
fun capture_goal label goal = (print(label ^ "="); print_term goal; print "\n");
val _ = capture_goal "ISR1_actual_goal" (List.nth(cases,0));
val _ = capture_goal "ISR2_actual_goal" (List.nth(cases,1));
val _ = capture_goal "ISR3_actual_goal" (List.nth(cases,2));
val _ = capture_goal "ISR4_actual_goal" (List.nth(cases,3));
val _ = capture_goal "ISR5_actual_goal" (List.nth(cases,4));
val _ = capture_goal "ISR6_actual_goal" (List.nth(cases,5));
val _ = capture_goal "ISR7_actual_goal" (List.nth(cases,6));
val _ = capture_goal "ISR8_actual_goal" (List.nth(cases,7));
val _ = capture_goal "ISR9_actual_goal" (List.nth(cases,8));
val _ = capture_goal "ISR10_actual_goal" (List.nth(cases,9));
val _ = capture_goal "ISR11_actual_goal" (List.nth(cases,10));
val _ = capture_goal "ISR12_actual_goal" (List.nth(cases,11));
val _ = capture_goal "ISR13_actual_goal" (List.nth(cases,12));
val _ = capture_goal "ISR14_actual_goal" (List.nth(cases,13));
val _ = capture_goal "ISR15_actual_goal" (List.nth(cases,14));
val _ = capture_goal "ISR16_actual_goal" (List.nth(cases,15));
val _ = capture_goal "ISR17_actual_goal" (List.nth(cases,16));
