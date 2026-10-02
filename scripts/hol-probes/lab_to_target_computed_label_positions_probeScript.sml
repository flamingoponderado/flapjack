load "bossLib";
load "preamble";
load "lab_to_targetProofTheory";
open bossLib HolKernel Parse preamble lab_to_targetProofTheory lab_to_targetTheory labLangTheory labPropsTheory labSemTheory sptreeTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun types label th = (print(label ^ "="); app (fn v => print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";")) (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val original_lookup = Q.prove(`
  ∀pos sec_list acc l1 l2 x2 c labs ffis nop.
      EVERY sec_labels_ok sec_list /\
      ALL_DISTINCT (MAP Section_num sec_list) ∧
      EVERY (ALL_DISTINCT o extract_labels o Section_lines) sec_list ∧
      EVERY sec_label_zero sec_list /\
      all_enc_ok c labs ffis pos sec_list /\
      loc_to_pc l1 l2 sec_list = SOME x2 ==>
      lab_lookup l1 l2 (compute_labels_alt pos sec_list acc) =
      SOME (pos_val x2 pos sec_list)`,
  ho_match_mp_tac compute_labels_alt_ind>>fs[]>>
  CONJ_TAC >- (rw[]>> fs[compute_labels_alt_def,loc_to_pc_def])
  \\ rw[compute_labels_alt_def,pos_val_thm]
  \\ pop_assum mp_tac
  \\ simp[Once loc_to_pc_thm]
  \\ pairarg_tac \\ fs[]
  \\ fs[all_enc_ok_cons]
  \\ old_drule lines_ok_lines_enc_with_nop \\ strip_tac
  \\ old_drule lines_enc_with_nop_length_ok \\ strip_tac
  \\ IF_CASES_TAC \\ fs[]
  >- (
    rveq
    \\ TOP_CASE_TAC
    >- (
      Cases_on`loc_to_pc k l2 sec_list` \\ fs[]
      \\ strip_tac \\ rveq
      \\ qmatch_goalsub_abbrev_tac`sec_pos_val i pos lines`
      \\ qspecl_then[`i`,`pos`,`lines`]mp_tac sec_pos_val_too_big
      \\ impl_tac >- simp[Abbr`i`]
      \\ simp[] \\ strip_tac
      \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac section_labels_sec_length \\ rw[]
      \\ qspecl_then[`lines`,`pos`]mp_tac sec_length_sum_line_length \\ rw[] \\ fs[]
      \\ first_x_assum match_mp_tac \\ asm_exists_tac \\ fs[])
    \\ strip_tac \\ rveq
    \\ simp[lab_lookup_compute_labels_alt_ignore]
    \\ simp[lab_lookup_def]
    \\ Cases_on`l2=0`
    >- (
      simp[lookup_fromAList]
      \\ fs[Once sec_loc_to_pc_def]
      \\ rveq
      \\ imp_res_tac lines_enc_with_nop_label_zero
      \\ Cases_on`EVERY is_Label lines`
      >- (
        `FILTER ($~ o is_Label) lines = []`
        by srw_tac[ETA_ss][FILTER_EQ_NIL] \\ simp[]
        \\ simp[EVERY_is_Label_sec_pos_val]
        \\ imp_res_tac pos_val_0 \\ simp[]
        \\ `SUM (MAP line_length lines) = 0` suffices_by simp[]
        \\ rw[SUM_eq_0,MEM_MAP] \\ fs[EVERY_MEM]
        \\ res_tac
        \\ Cases_on`y` \\ fs[line_length_def] )
      \\ imp_res_tac sec_pos_val_0
      \\ simp[] )
    \\ simp[lookup_fromAList]
    \\ old_drule (GEN_ALL ALOOKUP_section_labels)
    \\ fs[sec_label_zero_def]
    \\ disch_then old_drule \\ simp[]
    \\ disch_then(qspecl_then[`pos`,`[]`]strip_assume_tac) \\ rfs[]
    \\ match_mp_tac EQ_SYM
    \\ simp[lookup_insert, lookup_fromAList]
    \\ match_mp_tac pos_val_0
    \\ asm_exists_tac \\ fs[])
  \\ strip_tac
  \\ rveq
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`sec_pos_val i pos lines`
  \\ qspecl_then[`i`,`pos`,`lines`]mp_tac sec_pos_val_too_big
  \\ impl_tac >- simp[Abbr`i`]
  \\ simp[] \\ strip_tac
  \\ qspecl_then[`pos`,`lines`,`[]`]mp_tac section_labels_sec_length \\ rw[]
  \\ qspecl_then[`lines`,`pos`]mp_tac sec_length_sum_line_length \\ rw[] \\ fs[]
  \\ first_x_assum match_mp_tac \\ asm_exists_tac \\ fs[]);
val _=capture "lab_lookup_compute_labels_test" original_lookup;
val _=types "lab_lookup_compute_labels_test_types" original_lookup;
val _=print("hypotheses="^Int.toString(length(hyp original_lookup))^"\n");
val _=show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc((QCONV(SIMP_CONV(srw_ss())[loc_to_pc_def,sec_loc_to_pc_def]) THENC EVAL THENC QCONV(SIMP_CONV(srw_ss())[])) q)); print "\n");
val _=observe "head_zero" ``loc_to_pc 1 0 ([Section 1 []]:8 sec list) = SOME 0 /\ lab_lookup 1 0 (compute_labels_alt 18 [Section 1 []] (fromAList [(1,fromAList [(0,999)])])) = SOME 18 /\ pos_val 0 18 [Section 1 []] = 18``;
val _=observe "trailing_label" ``loc_to_pc 1 7 ([Section 1 [Asm (Asmi (Inst Skip)) [1w;2w] 2;Label 1 7 0];Section 2 []]:8 sec list) = SOME 1 /\ lab_lookup 1 7 (compute_labels_alt 18 [Section 1 [Asm (Asmi (Inst Skip)) [1w;2w] 2;Label 1 7 0];Section 2 []] (fromAList [(1,fromAList [(7,999)])])) = SOME 20 /\ pos_val 1 18 [Section 1 [Asm (Asmi (Inst Skip)) [1w;2w] 2;Label 1 7 0];Section 2 []] = 20``;
val _=observe "next_instruction" ``loc_to_pc 1 7 ([Section 1 [Label 1 7 0];Section 2 [Asm (Asmi (Inst Skip)) [1w;2w] 2]]:8 sec list) = SOME 0 /\ lab_lookup 1 7 (compute_labels_alt 18 [Section 1 [Label 1 7 0];Section 2 [Asm (Asmi (Inst Skip)) [1w;2w] 2]] (fromAList [(1,fromAList [(7,999)])])) = SOME 18 /\ pos_val 0 18 [Section 1 [Label 1 7 0];Section 2 [Asm (Asmi (Inst Skip)) [1w;2w] 2]] = 18``;
val _=observe "tail_section" ``loc_to_pc 2 7 ([Section 1 [Asm (Asmi (Inst Skip)) [1w;2w] 2];Section 2 [Label 2 7 0;LabAsm Halt 0w [3w;4w] 2]]:8 sec list) = SOME 1 /\ lab_lookup 2 7 (compute_labels_alt 18 [Section 1 [Asm (Asmi (Inst Skip)) [1w;2w] 2];Section 2 [Label 2 7 0;LabAsm Halt 0w [3w;4w] 2]] (fromAList [(2,fromAList [(7,999)])])) = SOME 20 /\ pos_val 1 18 [Section 1 [Asm (Asmi (Inst Skip)) [1w;2w] 2];Section 2 [Label 2 7 0;LabAsm Halt 0w [3w;4w] 2]] = 20``;
val _=observe "empty_prefix" ``loc_to_pc 2 7 ([Section 1 [];Section 2 [Label 2 7 0]]:8 sec list) = SOME 0 /\ lab_lookup 2 7 (compute_labels_alt 18 [Section 1 [];Section 2 [Label 2 7 0]] (fromAList [(2,fromAList [(7,999)])])) = SOME 18 /\ pos_val 0 18 [Section 1 [];Section 2 [Label 2 7 0]] = 18``;
