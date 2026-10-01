(* Full original re-encoding similarity statements and inferred types.
Local lemmas are literal source proof replays, not exported theorem claims. *)
load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory;
val source_LIST_REL_enc_line = prove (``  ∀ls ls'.
  LIST_REL line_similar ls ls' ⇔
  LIST_REL line_similar (MAP (enc_line enc len) ls) ls'``,
  Induct>>rw[]>>Cases_on`h`>>rw[enc_line_def,EQ_IMP_THM]>>Cases_on`y`>>
  fs[line_similar_def]);
val source_enc_lines_again_IMP_similar = prove (``  ∀labs ffis pos enc lines acc ok lines' ok' curr.
  enc_lines_again labs ffis pos enc lines (acc,ok) = (lines',ok') ⇒
  LIST_REL line_similar curr (REVERSE acc) ⇒
  LIST_REL line_similar (curr++lines) lines'``,
  Induct_on`lines`>>fs[enc_lines_again_def]>>rw[]>>
  fs[AND_IMP_INTRO]>>
  `curr ++ h ::lines = SNOC h curr ++ lines` by fs[]>>
  pop_assum SUBST1_TAC>>
  first_assum match_mp_tac>>
  Cases_on`h`>>fs[enc_lines_again_def]>>EVERY_CASE_TAC>>
  asm_exists_tac>>fs[SNOC_APPEND,line_similar_def]);
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "es_line" source_LIST_REL_enc_line;
val _ = captureTypes "es_line_types" source_LIST_REL_enc_line;
val _ = capture "es_initial" (DB.fetch "lab_to_targetProof" "code_similar_enc_sec_list");
val _ = captureTypes "es_initial_types" (DB.fetch "lab_to_targetProof" "code_similar_enc_sec_list");
val _ = capture "es_again" source_enc_lines_again_IMP_similar;
val _ = captureTypes "es_again_types" source_enc_lines_again_IMP_similar;
val _ = capture "es_sections" (DB.fetch "lab_to_targetProof" "enc_secs_again_IMP_similar");
val _ = captureTypes "es_sections_types" (DB.fetch "lab_to_targetProof" "enc_secs_again_IMP_similar");
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = observe "es_initial_value" ``enc_sec_list (\a:8 asm. [2w;3w;4w]) [Section 4 ([Label 1 2 1; Asm (Asmi (asm$Inst asm$Skip)) [6w] 1; LabAsm (Jump (Lab 1 2)) 7w [7w] 1] : 8 line list)]``;
val _ = observe "es_again_growth" ``enc_lines_again LN [] 0 (\a:8 asm. [2w;3w;4w]) ([Label 1 2 1; Asm (Asmi (asm$Inst asm$Skip)) [6w] 1; LabAsm (Jump (Lab 1 2)) 7w [7w] 1] : 8 line list) ([],T)``;
val _ = observe "es_again_unchanged" ``enc_lines_again LN [] 2 (\a:8 asm. [2w;3w;4w]) ([LabAsm (Jump (Lab 1 2)) 254w [7w] 4]:8 line list) ([Asm (Asmi (asm$Inst asm$Skip)) [9w] 4],F)``;
val _ = observe "es_again_no_growth" ``enc_lines_again LN [] 2 (\a:8 asm. [2w;3w;4w]) ([LabAsm (Jump (Lab 1 2)) 7w [7w] 4]:8 line list) ([Asm (Asmi (asm$Inst asm$Skip)) [9w] 4],T)``;
val _ = observe "es_sections_value" ``enc_secs_again 0 LN [] (\a:8 asm. [2w;3w;4w]) [Section 4 ([Label 1 2 1; Asm (Asmi (asm$Inst asm$Skip)) [6w] 1; LabAsm (Jump (Lab 1 2)) 7w [7w] 1] : 8 line list);Section 8 []]``;
val _ = observe "es_sections_similar" ``code_similar [Section 4 ([Label 1 2 1; Asm (Asmi (asm$Inst asm$Skip)) [6w] 1; LabAsm (Jump (Lab 1 2)) 7w [7w] 1] : 8 line list);Section 8 []] (FST(enc_secs_again 0 LN [] (\a:8 asm. [2w;3w;4w]) [Section 4 ([Label 1 2 1; Asm (Asmi (asm$Inst asm$Skip)) [6w] 1; LabAsm (Jump (Lab 1 2)) 7w [7w] 1] : 8 line list);Section 8 []]))``;
