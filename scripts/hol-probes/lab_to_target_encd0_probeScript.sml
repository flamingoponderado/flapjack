load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labPropsTheory labLangTheory labSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "line_encd0_def" line_encd0_def;
val _ = types "line_encd0_def_types" line_encd0_def;
val _ = capture "sec_encd0_def" sec_encd0_def;
val _ = types "sec_encd0_def_types" sec_encd0_def;
val all_encd0_term = ``all_encd0``;
val _ = temp_clear_overloads_on "all_encd0";
val _ = (print "all_encd0=";print_term all_encd0_term;print "\n");
val _ = (print "all_encd0_types="; print(type_to_string(type_of all_encd0_term));print "\n");
val _ = temp_overload_on ("all_encd0", all_encd0_term);
val enc_sec_list_encd0 = prove (``∀ls. all_encd0 enc (enc_sec_list enc ls)``,
  Induct \\ fs[enc_sec_list_def]
  \\ Cases \\ simp[enc_sec_def,EVERY_MAP]
  \\ simp[EVERY_MEM]
  \\ Cases \\ simp[enc_line_def,line_encd0_def]
  \\ metis_tac[]);
val _ = capture "enc_sec_list_encd0" enc_sec_list_encd0;
val _ = types "enc_sec_list_encd0_types" enc_sec_list_encd0;
val enc_lines_again_encd0 = prove (``∀labs ffis pos enc lines acc ok res ok'.
    enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') ∧
    EVERY (line_encd0 enc) lines ∧
    EVERY (line_encd0 enc) acc ⇒
    EVERY (line_encd0 enc) res``,
  recInduct enc_lines_again_ind
  \\ rw[enc_lines_again_def]
  \\ rw[EVERY_REVERSE] \\ fs[]
  \\ fs[line_encd0_def]
  \\ first_x_assum match_mp_tac
  \\ rw[MAX_DEF] \\ metis_tac[]);
val _ = capture "enc_lines_again_encd0" enc_lines_again_encd0;
val _ = types "enc_lines_again_encd0_types" enc_lines_again_encd0;
val enc_secs_again_encd0 = prove (``∀pos labs ffis enc ls res ok.
    enc_secs_again pos labs ffis enc ls = (res,ok) ∧
    all_encd0 enc ls ⇒
    all_encd0 enc res``,
  ho_match_mp_tac enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ fs[] \\ rw[]
  \\ match_mp_tac enc_lines_again_encd0
  \\ asm_exists_tac \\ fs[]);
val _ = capture "enc_secs_again_encd0" enc_secs_again_encd0;
val _ = types "enc_secs_again_encd0_types" enc_secs_again_encd0;
val lines_upd_lab_len_encd0 = prove (``∀pos ls acc.
    EVERY (line_encd0 enc) ls ∧
    EVERY (line_encd0 enc) acc ⇒
    EVERY (line_encd0 enc) (FST (lines_upd_lab_len pos ls acc))``,
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def]
  \\ fs[EVERY_REVERSE,line_encd0_def]);
val _ = capture "lines_upd_lab_len_encd0" lines_upd_lab_len_encd0;
val _ = types "lines_upd_lab_len_encd0_types" lines_upd_lab_len_encd0;
val upd_lab_len_encd0 = prove (``∀pos ss. all_encd0 enc ss ⇒ all_encd0 enc (upd_lab_len pos ss)``,
  recInduct upd_lab_len_ind
  \\ rw[upd_lab_len_def] \\ fs[]
  \\ rw[UNCURRY]
  >- (
    match_mp_tac lines_upd_lab_len_encd0
    \\ fs[])
  \\ first_x_assum match_mp_tac
  \\ metis_tac[PAIR]);
val _ = capture "upd_lab_len_encd0" upd_lab_len_encd0;
val _ = types "upd_lab_len_encd0_types" upd_lab_len_encd0;
val _ = show_types := false;
val exists_nonzero8 = prove (``∃w:word8. w ≠ 0w``, qexists_tac `1w` THEN EVAL_TAC);
fun observe label q = (print(label ^ "="); print_term(rconc(
 (SIMP_CONV(srw_ss())[line_encd0_def,sec_encd0_def] THENC EVAL
 THENC SIMP_CONV(srw_ss())[COND_RAND,COND_RATOR,exists_nonzero8] THENC EVAL) q));print "\n");
val shrink = ``(λa:8 asm. case a of Jump w => if w = 0w then [0w;0w;0w;0w] else [1w;1w] | _ => [99w;99w]) : 8 asm -> word8 list``;
val grow = ``(λa:8 asm. case a of Jump w => if w = 0w then [0w] else [1w;1w;1w] | _ => [99w;99w]) : 8 asm -> word8 list``;
val labs = ``insert 3 (insert 4 10 LN) LN : num num_map num_map``;
val sl = ``[LabAsm (Jump (Lab 3 4)) 0w [0w;0w;0w;0w] 4] : 8 labLang$line list``;
val gl = ``[LabAsm (Jump (Lab 3 4)) 0w [0w] 1] : 8 labLang$line list``;
val acc = ``[Label 1 7 99] : 8 labLang$line list``;
val code = ``[Section 1 ^sl;Section 2 []] : 8 labLang$prog``;
val _ = observe "label_annotation_unrestricted" ``line_encd0 ^shrink (Label 99 0 999:8 labLang$line)``;
val _ = observe "asm_cache_mismatch_rejected" ``~line_encd0 ^shrink (Asm (Asmi (Inst Skip)) [] 0)``;
val _ = observe "shrink_source_valid" ``EVERY (line_encd0 ^shrink) ^sl``;
val _ = observe "grow_source_valid" ``EVERY (line_encd0 ^grow) ^gl``;
val _ = observe "shrink_output_valid" ``EVERY (line_encd0 ^shrink) (FST(enc_lines_again ^labs [] 0 ^shrink ^sl (^acc,T)))``;
val _ = observe "grow_output_valid" ``EVERY (line_encd0 ^grow) (FST(enc_lines_again ^labs [] 0 ^grow ^gl ([],T)))``;
val _ = observe "shrink_full_output" ``enc_lines_again ^labs [] 0 ^shrink ^sl (^acc,T) = ([Label 1 7 99;LabAsm (Jump (Lab 3 4)) 10w [1w;1w] 4],(4,T))``;
val _ = observe "grow_full_output" ``enc_lines_again ^labs [] 0 ^grow ^gl ([],T) = ([LabAsm (Jump (Lab 3 4)) 10w [1w;1w;1w] 3],(3,F))``;
val _ = observe "equal_word_full_output" ``enc_lines_again ^labs [] 0 ^grow [LabAsm (Jump (Lab 3 4)) 10w [1w;1w;1w] 3] ([],F) = ([LabAsm (Jump (Lab 3 4)) 10w [1w;1w;1w] 3],(3,F))``;
val _ = observe "initial_code_valid" ``all_encd0 ^shrink (enc_sec_list ^shrink ^code)``;
val _ = observe "repeat_code_valid" ``all_encd0 ^shrink (FST(enc_secs_again 0 ^labs [] ^shrink ^code))``;
val _ = observe "update_lines_valid" ``EVERY (line_encd0 ^shrink) (FST(lines_upd_lab_len 3 ^sl ^acc))``;
val _ = observe "update_code_valid" ``all_encd0 ^shrink (upd_lab_len 3 ^code)``;
val _ = observe "grow_empty_encoder_initial" ``all_encd0 (λa:8 asm. []:word8 list) (enc_sec_list (λa:8 asm. []:word8 list) ^code)``;
