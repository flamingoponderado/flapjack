load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val _ = capture "code_similar_MAP_Section_num" code_similar_MAP_Section_num;
val _ = types "code_similar_MAP_Section_num_types" code_similar_MAP_Section_num;
val _ = capture "code_similar_extract_labels" code_similar_extract_labels;
val _ = types "code_similar_extract_labels_types" code_similar_extract_labels;
val _ = capture "line_similar_line_get_code_labels" line_similar_line_get_code_labels;
val _ = types "line_similar_line_get_code_labels_types" line_similar_line_get_code_labels;
val _ = capture "code_similar_get_code_labels" code_similar_get_code_labels;
val _ = types "code_similar_get_code_labels_types" code_similar_get_code_labels;
val _ = capture "line_similar_line_get_labels" line_similar_line_get_labels;
val _ = types "line_similar_line_get_labels_types" line_similar_line_get_labels;
val _ = capture "code_similar_get_labels" code_similar_get_labels;
val _ = types "code_similar_get_labels_types" code_similar_get_labels;
val _ = show_types := false;
open labPropsTheory labLangTheory;
fun observe label q = (print(label ^ "="); print_term(rconc(
 (SIMP_CONV(srw_ss())[code_similar_def,line_similar_def,extract_labels_def,
  get_labels_def,sec_get_labels_def,line_get_labels_def,labs_of_def,
  get_code_labels_def,sec_get_code_labels_def,line_get_code_labels_def]
  THENC EVAL THENC SIMP_CONV(srw_ss())[pred_setTheory.EXTENSION,
  pred_setTheory.GSPECIFICATION] THENC EVAL) q)); print "\n");
val left = ``[Section 10 [Label 99 7 5; LabAsm (Jump (Lab 3 4)) 123w [] 0;
 LabAsm (Call (Lab 8 9)) 0w [] 0; Label 10 7 0];Section 20 []] : 8 labLang$prog``;
val right = ``[Section 10 [Label 99 7 0; LabAsm (Jump (Lab 3 4)) 9w [255w] 37;
 LabAsm (Call (Lab 8 9)) 8w [1w;2w] 2; Label 10 7 99];Section 20 []] : 8 labLang$prog``;
val _ = observe "changed_encoding_similar" ``code_similar ^left ^right``;
val _ = observe "section_numbers" ``MAP Section_num ^right = [10;20]``;
val _ = observe "ordered_extraction" ``MAP (extract_labels o Section_lines) ^right = [[(99,7);(10,7)];[]]``;
val _ = observe "reference_hit" ``(3,4) IN get_labels ^right``;
val _ = observe "call_ignored" ``~((8,9) IN get_labels ^right)``;
val _ = observe "code_section_owner" ``(10,7) IN get_code_labels ^right``;
val _ = observe "code_wrong_owner" ``~((99,7) IN get_code_labels ^right)``;
val _ = observe "empty_section_zero" ``(20,0) IN get_code_labels ^right``;
val _ = observe "numbers_preserved" ``code_similar ^left ^right ==> MAP Section_num ^left = MAP Section_num ^right``;
val _ = observe "extraction_preserved" ``code_similar ^left ^right ==> MAP (extract_labels o Section_lines) ^left = MAP (extract_labels o Section_lines) ^right``;
val _ = observe "code_labels_preserved" ``code_similar ^left ^right ==> get_code_labels ^left = get_code_labels ^right``;
val _ = observe "references_preserved" ``code_similar ^left ^right ==> get_labels ^left = get_labels ^right``;
val _ = observe "label_names_preserved" ``line_similar (Label 99 7 5:8 labLang$line) (Label 99 7 0) ==> line_get_code_labels (Label 99 7 5:8 labLang$line) = line_get_code_labels (Label 99 7 0:8 labLang$line)``;
val _ = observe "line_refs_preserved" ``line_similar (LabAsm (Jump (Lab 3 4)) 123w [] 0:8 labLang$line) (LabAsm (Jump (Lab 3 4)) 9w [255w] 37) ==> line_get_labels (LabAsm (Jump (Lab 3 4)) 123w [] 0:8 labLang$line) = line_get_labels (LabAsm (Jump (Lab 3 4)) 9w [255w] 37:8 labLang$line)``;
val _ = observe "changed_reference_rejected" ``~line_similar (LabAsm (Jump (Lab 3 4)) 123w [] 0:8 labLang$line) (LabAsm (Jump (Lab 3 5)) 123w [] 0)``;
