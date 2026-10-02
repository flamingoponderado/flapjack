load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory labPropsTheory labSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
fun captureOps label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (find_terms (fn t => is_const t andalso fst(dest_const t)="pos_val") (concl th)); print "\n");
val _ = capture "line_length_def" line_length_def;
val _ = captureTypes "line_length_def_types" line_length_def;
val _ = capture "sec_pos_val_def" sec_pos_val_def;
val _ = captureTypes "sec_pos_val_def_types" sec_pos_val_def;
val _ = capture "sec_pos_val_too_big" sec_pos_val_too_big;
val _ = captureTypes "sec_pos_val_too_big_types" sec_pos_val_too_big;
val _ = capture "every_label_sec_pos_val" EVERY_is_Label_sec_pos_val;
val _ = captureTypes "every_label_sec_pos_val_types" EVERY_is_Label_sec_pos_val;
val _ = capture "pos_val_def" pos_val_def;
val _ = captureTypes "pos_val_def_types" pos_val_def;
val pos_val_thm0_source = prove (``∀i pos acc.
    pos_val i pos acc =
      case acc of [] => pos
      | Section k s :: ss =>
        case sec_pos_val i pos s of NONE =>
        pos_val (i - LENGTH (FILTER ($~ o is_Label) s)) (pos + SUM (MAP line_length s)) ss
        | SOME x => x``,
  ho_match_mp_tac pos_val_ind \\ rw[pos_val_def,sec_pos_val_def,ADD1]);
val _ = capture "pos_val_thm0" pos_val_thm0_source;
val _ = captureTypes "pos_val_thm0_types" pos_val_thm0_source;
val _ = capture "pos_val_thm" pos_val_thm;
val _ = captureTypes "pos_val_thm_types" pos_val_thm;
val _ = captureOps "pos_val_thm_operator_types" pos_val_thm;
val _ = capture "pos_val_acc" pos_val_acc;
val _ = captureTypes "pos_val_acc_types" pos_val_acc;
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc((SIMP_CONV (srw_ss()) [] THENC EVAL THENC SIMP_CONV (srw_ss()) [] THENC EVAL) q)); print "\n");
val lines = ``[Label 1 5 0; Label 1 6 42; Asm (Cbw 1 2) [1w;2w] 99; Label 1 7 100; LabAsm Halt 0w [3w;4w;5w] 88; Label 1 8 0] : 8 labLang$line list``;
val code = ``[Section 9 []; Section 1 ^lines; Section 2 [Label 2 4 2; Asm (Cbw 3 4) [6w] 100]; Section 3 []] : 8 labLang$prog``;
val _ = observe "label_zero_length" ``line_length (Label 1 5 0:1 labLang$line) = 0``;
val _ = observe "label_nonzero_length" ``line_length (Label 1 5 99:80 labLang$line) = 1``;
val _ = observe "asm_bytes_length" ``line_length (Asm (Cbw 1 2) [1w;2w] 99:8 labLang$line) = 2``;
val _ = observe "labasm_bytes_length" ``line_length (LabAsm Halt 0w [3w;4w;5w] 88:8 labLang$line) = 3``;
val _ = observe "sec_first" ``sec_pos_val 0 10 ^lines = SOME 11``;
val _ = observe "sec_second" ``sec_pos_val 1 10 ^lines = SOME 14``;
val _ = observe "sec_equal_exhaustion" ``sec_pos_val 2 10 ^lines = NONE``;
val _ = observe "sec_past_exhaustion" ``sec_pos_val 99 10 ^lines = NONE``;
val _ = observe "sec_labels_only" ``sec_pos_val 0 10 [Label 1 5 99; Label 1 6 0:80 labLang$line] = NONE``;
val _ = observe "code_first" ``pos_val 0 10 ^code = 11``;
val _ = observe "code_second" ``pos_val 1 10 ^code = 14``;
val _ = observe "code_third" ``pos_val 2 10 ^code = 18``;
val _ = observe "code_equal_exhaustion" ``pos_val 3 10 ^code = 19``;
val _ = observe "code_past_exhaustion" ``pos_val 99 10 ^code = 19``;
val _ = observe "code_empty_wide" ``pos_val 99 10 ([]:80 labLang$prog) = 10``;
