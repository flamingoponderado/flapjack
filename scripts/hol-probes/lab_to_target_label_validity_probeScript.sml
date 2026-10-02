load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labPropsTheory labLangTheory labSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val enc_sec_list_sec_labels_ok = prove (``∀enc code.
   EVERY sec_labels_ok code
   ⇒ EVERY sec_labels_ok (enc_sec_list enc code)``,
  rw[enc_sec_list_def,EVERY_MAP]
  \\ Induct_on`code` \\ fs[]
  \\ Cases \\ fs[sec_labels_ok_def,enc_sec_def,EVERY_MAP]
  \\ rw[] \\ fs[EVERY_MEM]
  \\ Cases \\ fs[enc_line_def]
  \\ strip_tac \\ res_tac \\ fs[]);
val _ = capture "enc_sec_list_sec_labels_ok" enc_sec_list_sec_labels_ok;
val _ = types "enc_sec_list_sec_labels_ok_types" enc_sec_list_sec_labels_ok;
val enc_lines_again_sec_labels_ok = prove (``∀labs ffis pos enc lines acc ok res ok' k.
    enc_lines_again labs ffis pos enc lines (acc,ok) = (res,ok') ∧
    EVERY (sec_label_ok k) acc ∧
    EVERY (sec_label_ok k) lines ⇒
    EVERY (sec_label_ok k) res``,
  recInduct enc_lines_again_ind \\ rw[enc_lines_again_def]
  \\ rw[EVERY_REVERSE]);
val _ = capture "enc_lines_again_sec_labels_ok" enc_lines_again_sec_labels_ok;
val _ = types "enc_lines_again_sec_labels_ok_types" enc_lines_again_sec_labels_ok;
val enc_secs_again_sec_labels_ok = prove (``∀pos ffis labs enc ls res ok k.
    enc_secs_again pos ffis labs enc ls = (res,ok) ∧ EVERY sec_labels_ok ls ⇒
    EVERY sec_labels_ok res``,
  recInduct enc_secs_again_ind
  \\ rw[enc_secs_again_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ match_mp_tac enc_lines_again_sec_labels_ok
  \\ asm_exists_tac \\ fs[]);
val _ = capture "enc_secs_again_sec_labels_ok" enc_secs_again_sec_labels_ok;
val _ = types "enc_secs_again_sec_labels_ok_types" enc_secs_again_sec_labels_ok;
val lines_upd_lab_len_sec_label_ok = prove (``∀pos lines acc k.
     EVERY (sec_label_ok k) lines ∧
     EVERY (sec_label_ok k) acc ⇒
     EVERY (sec_label_ok k) (FST (lines_upd_lab_len pos lines acc))``,
  recInduct lines_upd_lab_len_ind
  \\ rw[lines_upd_lab_len_def]
  \\ rw[EVERY_REVERSE]);
val _ = capture "lines_upd_lab_len_sec_label_ok" lines_upd_lab_len_sec_label_ok;
val _ = types "lines_upd_lab_len_sec_label_ok_types" lines_upd_lab_len_sec_label_ok;
val upd_lab_len_sec_labels_ok = prove (``∀n ls. EVERY sec_labels_ok ls ⇒ EVERY sec_labels_ok (upd_lab_len n ls)``,
  recInduct upd_lab_len_ind
  \\ rw[upd_lab_len_def]
  \\ pairarg_tac \\ fs[]
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac lines_upd_lab_len_sec_label_ok
  \\ rw[]);
val _ = capture "upd_lab_len_sec_labels_ok" upd_lab_len_sec_labels_ok;
val _ = types "upd_lab_len_sec_labels_ok_types" upd_lab_len_sec_labels_ok;
val add_nop_sec_label_ok = prove (``∀nop aux.
    EVERY (sec_label_ok k) aux ⇒
    EVERY (sec_label_ok k) (add_nop nop aux)``,
  recInduct add_nop_ind
  \\ rw[add_nop_def]);
val _ = capture "add_nop_sec_label_ok" add_nop_sec_label_ok;
val _ = types "add_nop_sec_label_ok_types" add_nop_sec_label_ok;
val pad_section_sec_label_ok = prove (``∀nop xs acc k.
    EVERY (sec_label_ok k) xs ∧
    EVERY (sec_label_ok k) acc ⇒
    EVERY (sec_label_ok k) (pad_section nop xs acc)``,
  recInduct pad_section_ind
  \\ rw[pad_section_def]
  \\ rw[EVERY_REVERSE] \\ fs[]
  \\ first_x_assum match_mp_tac
  \\ metis_tac[add_nop_sec_label_ok]);
val _ = capture "pad_section_sec_label_ok" pad_section_sec_label_ok;
val _ = types "pad_section_sec_label_ok_types" pad_section_sec_label_ok;
val pad_code_sec_labels_ok = prove (``∀nop code.
    EVERY sec_labels_ok code ⇒
    EVERY sec_labels_ok (pad_code nop code)``,
  recInduct pad_code_ind
  \\ rw[pad_code_def]
  \\ match_mp_tac pad_section_sec_label_ok
  \\ rw[]);
val _ = capture "pad_code_sec_labels_ok" pad_code_sec_labels_ok;
val _ = types "pad_code_sec_labels_ok_types" pad_code_sec_labels_ok;
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val enc = ``(λa:8 asm. [0w;1w]:word8 list)``;
val ls = ``[Label 1 1 1; Asm (Asmi (Inst Skip)) [10w] 1;
 LabAsm (Jump (Lab 3 4)) 99w [11w;12w] 2; Label 1 3 0] : 8 labLang$line list``;
val acc = ``[Label 1 2 3; Asm (Asmi (Inst Skip)) [20w] 1] : 8 labLang$line list``;
val code = ``[Section 1 ^ls;Section 2 []] : 8 labLang$prog``;
val labs = ``LN : num num_map num_map``;
val _ = observe "source_valid" ``EVERY (sec_label_ok 1) ^ls``;
val _ = observe "acc_valid" ``EVERY (sec_label_ok 1) ^acc``;
val _ = observe "initial_encode_valid" ``EVERY sec_labels_ok (enc_sec_list ^enc ^code)``;
val _ = observe "repeat_acc_valid" ``EVERY (sec_label_ok 1) (FST (enc_lines_again ^labs [] 3 ^enc ^ls (^acc,F)))``;
val _ = observe "repeat_code_valid" ``EVERY sec_labels_ok (FST (enc_secs_again 3 ^labs [] ^enc ^code))``;
val _ = observe "update_odd_valid" ``EVERY (sec_label_ok 1) (FST (lines_upd_lab_len 3 ^ls ^acc))``;
val _ = observe "update_even_valid" ``EVERY (sec_label_ok 1) (FST (lines_upd_lab_len 4 ^ls ^acc))``;
val _ = observe "update_code_valid" ``EVERY sec_labels_ok (upd_lab_len 3 ^code)``;
val _ = observe "add_nop_valid" ``EVERY (sec_label_ok 1) (add_nop [0w;0w] ^ls)``;
val _ = observe "empty_nop_valid" ``EVERY (sec_label_ok 1) (add_nop [] ^ls)``;
val _ = observe "padding_acc_valid" ``EVERY (sec_label_ok 1) (pad_section [0w;0w] ^ls ^acc)``;
val _ = observe "padding_code_valid" ``EVERY sec_labels_ok (pad_code [0w;0w] ^code)``;
val _ = observe "repeat_false_flag" ``~SND(SND(enc_lines_again ^labs [] 3 ^enc ^ls (^acc,F)))``;
val _ = observe "encoded_bad_label_rejected" ``~sec_labels_ok (Section 1 (MAP (enc_line ^enc 0) [Label 2 0 3]))``;
val _ = observe "padded_bad_label_rejected" ``~EVERY (sec_label_ok 1) (pad_section [0w] [Label 2 0 3:8 labLang$line] [] )``;
val _ = observe "update_label_order" ``extract_labels (FST(lines_upd_lab_len 3 ^ls ^acc)) = [(1,2);(1,1);(1,3)]``;
val _ = observe "repeat_label_order" ``extract_labels (FST(enc_lines_again ^labs [] 3 ^enc ^ls (^acc,F))) = [(1,2);(1,1);(1,3)]``;
val _ = observe "padding_label_order" ``extract_labels (pad_section [0w;0w] ^ls ^acc) = [(1,2);(1,1);(1,3)]``;
