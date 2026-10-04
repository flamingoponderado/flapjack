load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse bossLib preamble wordConvsTheory wordLangTheory
  word_instTheory word_unreachTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
(* Each local statement and proof copied unchanged from pinned original source. *)
val word_good_handlers_inst_select_exp = GEN_ALL(prove(``
∀a b c exp.
  word_good_handlers n (inst_select_exp a b c exp)
``,
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>
  fs[inst_select_exp_def]>>
  every_case_tac>>fs[inst_select_exp_def]
));
val _ = if null(hyp word_good_handlers_inst_select_exp) andalso null(free_vars(concl word_good_handlers_inst_select_exp)) then () else raise Fail "open word_good_handlers_inst_select_exp";
val _ = (print "goodHandlers_instSelectExp_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl word_good_handlers_inst_select_exp));
val _ = print("goodHandlers_instSelectExp_proved=" ^ term_to_string(rhs(concl(EQT_INTRO word_good_handlers_inst_select_exp))) ^ "\n");
val _ = print("goodHandlers_instSelectExp_hypotheses=" ^ Int.toString(length(hyp word_good_handlers_inst_select_exp)) ^ "\n");
val word_good_handlers_inst_select = GEN_ALL(prove(``
∀ac v ps.
  word_good_handlers n (inst_select ac v ps) ⇔
  word_good_handlers n ps
``,
  ho_match_mp_tac inst_select_ind>>rw[]>>
  fs[inst_select_def]>>
  every_case_tac>>fs[word_good_handlers_inst_select_exp]
));
val _ = if null(hyp word_good_handlers_inst_select) andalso null(free_vars(concl word_good_handlers_inst_select)) then () else raise Fail "open word_good_handlers_inst_select";
val _ = (print "goodHandlers_instSelect_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl word_good_handlers_inst_select));
val _ = print("goodHandlers_instSelect_proved=" ^ term_to_string(rhs(concl(EQT_INTRO word_good_handlers_inst_select))) ^ "\n");
val _ = print("goodHandlers_instSelect_hypotheses=" ^ Int.toString(length(hyp word_good_handlers_inst_select)) ^ "\n");
val word_good_handlers_three_to_two_reg_prog = GEN_ALL(prove(``
∀ps.
  word_good_handlers n (three_to_two_reg_prog b ps) ⇔
  word_good_handlers n ps
``,
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>rw[]>>
  fs[three_to_two_reg_def]>>
  every_case_tac>>fs[]
));
val _ = if null(hyp word_good_handlers_three_to_two_reg_prog) andalso null(free_vars(concl word_good_handlers_three_to_two_reg_prog)) then () else raise Fail "open word_good_handlers_three_to_two_reg_prog";
val _ = (print "goodHandlers_threeToTwoRegProg_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl word_good_handlers_three_to_two_reg_prog));
val _ = print("goodHandlers_threeToTwoRegProg_proved=" ^ term_to_string(rhs(concl(EQT_INTRO word_good_handlers_three_to_two_reg_prog))) ^ "\n");
val _ = print("goodHandlers_threeToTwoRegProg_hypotheses=" ^ Int.toString(length(hyp word_good_handlers_three_to_two_reg_prog)) ^ "\n");
val word_good_handlers_SimpSeq = GEN_ALL(prove(``
word_good_handlers n ps /\ word_good_handlers n qs ⇒
  word_good_handlers n (SimpSeq ps qs)
``,
  qid_spec_tac ‘ps’ \\
  Induct \\ simp[SimpSeq_def] \\
  Cases_on `qs = Skip` \\ fs[] \\
  fs[oneline dest_Seq_Move_def] \\
  every_case_tac \\ fs[]
));
val _ = if null(hyp word_good_handlers_SimpSeq) andalso null(free_vars(concl word_good_handlers_SimpSeq)) then () else raise Fail "open word_good_handlers_SimpSeq";
val _ = (print "goodHandlers_simpSeq_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl word_good_handlers_SimpSeq));
val _ = print("goodHandlers_simpSeq_proved=" ^ term_to_string(rhs(concl(EQT_INTRO word_good_handlers_SimpSeq))) ^ "\n");
val _ = print("goodHandlers_simpSeq_hypotheses=" ^ Int.toString(length(hyp word_good_handlers_SimpSeq)) ^ "\n");
val word_good_handlers_Seq_assoc_right = GEN_ALL(prove(``
word_good_handlers n ps /\ word_good_handlers n qs ⇒
  word_good_handlers n (Seq_assoc_right ps qs)
``,
  qid_spec_tac ‘qs’
  \\ qid_spec_tac ‘ps’
  \\ ho_match_mp_tac Seq_assoc_right_ind
  \\ simp[Seq_assoc_right_def]
  \\ rw[] \\ every_case_tac \\ fs[]
  \\ irule word_good_handlers_SimpSeq
  \\ fs[]
));
val _ = if null(hyp word_good_handlers_Seq_assoc_right) andalso null(free_vars(concl word_good_handlers_Seq_assoc_right)) then () else raise Fail "open word_good_handlers_Seq_assoc_right";
val _ = (print "goodHandlers_seqAssocRight_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl word_good_handlers_Seq_assoc_right));
val _ = print("goodHandlers_seqAssocRight_proved=" ^ term_to_string(rhs(concl(EQT_INTRO word_good_handlers_Seq_assoc_right))) ^ "\n");
val _ = print("goodHandlers_seqAssocRight_hypotheses=" ^ Int.toString(length(hyp word_good_handlers_Seq_assoc_right)) ^ "\n");
val word_good_handlers_remove_unreach = GEN_ALL(prove(``
word_good_handlers n ps ⇒
  word_good_handlers n (remove_unreach ps)
``,
  simp[remove_unreach_def] \\ disch_tac \\
  irule word_good_handlers_Seq_assoc_right \\
  fs[]
  \\ qmatch_goalsub_abbrev_tac `Seq_assoc_right ps s`
  \\ qid_spec_tac ‘s’
  \\ qid_spec_tac ‘ps’
  \\ ho_match_mp_tac Seq_assoc_right_ind
  \\ unabbrev_all_tac \\ simp[Seq_assoc_right_def]
  \\ simp[SimpSeq_def]
  \\ rw[]
 \\ every_case_tac \\ fs[]
));
val _ = if null(hyp word_good_handlers_remove_unreach) andalso null(free_vars(concl word_good_handlers_remove_unreach)) then () else raise Fail "open word_good_handlers_remove_unreach";
val _ = (print "goodHandlers_removeUnreach_typed="; Lib.with_flag (Globals.show_types,true) print_term(concl word_good_handlers_remove_unreach));
val _ = print("goodHandlers_removeUnreach_proved=" ^ term_to_string(rhs(concl(EQT_INTRO word_good_handlers_remove_unreach))) ^ "\n");
val _ = print("goodHandlers_removeUnreach_hypotheses=" ^ Int.toString(length(hyp word_good_handlers_remove_unreach)) ^ "\n");
