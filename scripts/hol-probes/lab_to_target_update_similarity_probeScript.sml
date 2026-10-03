load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val lines_upd_lab_len_AUX = Q.prove(
  `!l aux pos.
      REVERSE aux ++ FST (lines_upd_lab_len pos l []) =
      FST (lines_upd_lab_len pos l aux)`,
  Induct \\ fs [lines_upd_lab_len_def]
  \\ Cases \\ simp_tac std_ss [lines_upd_lab_len_def,LET_DEF]
  \\ pop_assum (fn th => once_rewrite_tac [GSYM th]) \\ fs []) |> GSYM

;
val line_similar_lines_upd_lab_len = prove (``!l aux pos l1.
      LIST_REL line_similar (FST (lines_upd_lab_len pos l [])) l1 =
      LIST_REL line_similar l l1``,
Induct \\ fs [lines_upd_lab_len_def]
  \\ Cases \\ fs [lines_upd_lab_len_def]
  \\ once_rewrite_tac [lines_upd_lab_len_AUX]
  \\ fs [] \\ rw [] \\ eq_tac \\ rw []
  \\ Cases_on `y` \\ fs [line_similar_def]);
val _ = capture "lines_upd_lab_len_AUX" lines_upd_lab_len_AUX;
val _ = types "lines_upd_lab_len_AUX_types" lines_upd_lab_len_AUX;
val _ = capture "line_similar_lines_upd_lab_len" line_similar_lines_upd_lab_len;
val _ = types "line_similar_lines_upd_lab_len_types" line_similar_lines_upd_lab_len;
val _ = capture "code_similar_upd_lab_len" code_similar_upd_lab_len;
val _ = types "code_similar_upd_lab_len_types" code_similar_upd_lab_len;
val _ = capture "lines_upd_lab_len_similar" lines_upd_lab_len_similar;
val _ = types "lines_upd_lab_len_similar_types" lines_upd_lab_len_similar;
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val lines = ``[Label 3 4 99;Asm (Asmi (Inst Skip)) [12w] 2;LabAsm (Jump (Lab 3 4)) 77w [] 5;Label 3 5 77] : 8 labLang$line list``;
val acc = ``[Label 9 8 91;Asm (Asmi (Inst Skip)) [] 77] : 8 labLang$line list``;
val target = ``[Label 3 4 777;Asm (Asmi (Inst Skip)) [] 999;LabAsm (Jump (Lab 3 4)) 0w [99w] 123;Label 3 5 999] : 8 labLang$line list``;
val updated = ``[Label 3 4 0;Asm (Asmi (Inst Skip)) [12w] 2;LabAsm (Jump (Lab 3 4)) 77w [] 5;Label 3 5 1] : 8 labLang$line list``;
val _ = observe "empty_acc_full" ``lines_upd_lab_len 3 [] ^acc = (REVERSE ^acc,3)``;
val _ = observe "even_full" ``lines_upd_lab_len 0 ^lines [] = (^updated,8)``;
val _ = observe "odd_full" ``lines_upd_lab_len 1 ^lines [] = ([Label 3 4 1;Asm (Asmi (Inst Skip)) [12w] 2;LabAsm (Jump (Lab 3 4)) 77w [] 5;Label 3 5 1],10)``;
val _ = observe "acc_full" ``lines_upd_lab_len 0 ^lines ^acc = (REVERSE ^acc ++ ^updated,8)``;
val _ = observe "aux_equality" ``FST(lines_upd_lab_len 0 ^lines ^acc) = REVERSE ^acc ++ FST(lines_upd_lab_len 0 ^lines [])``;
val _ = observe "line_relation_positive" ``LIST_REL line_similar (FST(lines_upd_lab_len 0 ^lines [])) ^target ∧ LIST_REL line_similar ^lines ^target``;
val _ = observe "line_relation_negative" ``¬LIST_REL line_similar (FST(lines_upd_lab_len 0 ^lines [])) [Label 3 8 0] ∧ ¬LIST_REL line_similar ^lines [Label 3 8 0]``;
val _ = observe "raw_changed_similarity_retained" ``FST(lines_upd_lab_len 0 ^lines []) <> ^lines ∧ LIST_REL line_similar (FST(lines_upd_lab_len 0 ^lines [])) ^lines``;
val _ = observe "code_relation_positive" ``code_similar (upd_lab_len 0 [Section 3 ^lines;Section 7 []]) [Section 3 ^target;Section 7 []] ∧ code_similar [Section 3 ^lines;Section 7 []] [Section 3 ^target;Section 7 []]``;
val _ = observe "section_id_mismatch_rejected" ``¬code_similar (upd_lab_len 0 [Section 3 ^lines]) [Section 4 ^target] ∧ ¬code_similar [Section 3 ^lines] [Section 4 ^target]``;
val _ = observe "instruction_mismatch_rejected" ``¬LIST_REL line_similar (FST(lines_upd_lab_len 0 [Asm (Asmi (Inst Skip)) [] 2] [])) [Asm (Asmi (Jump 0w)) [] 2] ∧ ¬LIST_REL line_similar [Asm (Asmi (Inst Skip)) [] 2] [Asm (Asmi (Jump 0w)) [] 2]``;
val _ = observe "accumulator_similarity" ``LIST_REL line_similar (FST(lines_upd_lab_len 0 ^lines ^acc)) (REVERSE ^acc ++ ^lines)``;
val _ = observe "empty_code" ``upd_lab_len 0 ([]:8 labLang$sec list) = [] ∧ code_similar (upd_lab_len 0 ([]:8 labLang$sec list)) []``;
val _ = observe "program_full" ``upd_lab_len 0 [Section 3 ^lines;Section 7 []] = [Section 3 ^updated;Section 7 []]``;
