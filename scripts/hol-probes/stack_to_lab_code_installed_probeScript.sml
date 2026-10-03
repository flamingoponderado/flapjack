load "preamble"; load "stack_to_labProofTheory";
open HolKernel Parse bossLib preamble stack_to_labProofTheory stack_to_labTheory
 labSemTheory labPropsTheory stackSemTheory;
val _ = Globals.linewidth := 1000000;
(* The script-local simpset changes of stack_to_labProofScript.sml:16-21. *)
val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
fun checked label th =
  (if null (hyp th) then () else raise Fail "open HOL hypotheses";
   print (label ^ "="); print_term (concl th); print "\n");

(* Exported originals of stack_to_labProofScript.sml:32-600. *)
val _ = checked "word_sh_word_shift_statement" (GEN_ALL word_sh_word_shift);
val _ = checked "assert_T_statement" (GEN_ALL assert_T);
val _ = checked "asm_fetch_aux_no_label_statement" (GEN_ALL asm_fetch_aux_no_label);
val _ = checked "dest_to_loc_def_statement" dest_to_loc_def;
val _ = checked "dest_to_loc_prime_def_statement" dest_to_loc'_def;
val _ = checked "find_code_lookup_statement" (GEN_ALL find_code_lookup);
val _ = checked "not_is_Label_compile_jump_statement" (GEN_ALL not_is_Label_compile_jump);
val _ = checked "word_cmp_not_NONE_statement" (GEN_ALL word_cmp_not_NONE);
val _ = checked "word_cmp_negate_alt_statement" (GEN_ALL word_cmp_negate_alt);
val _ = checked "word_cmp_negate_statement" (GEN_ALL word_cmp_negate);
val _ = checked "code_installed_def_statement" code_installed_def;
val _ = checked "code_installed_append_imp_statement" code_installed_append_imp;
val _ = checked "loc_to_pc_APPEND_statement" loc_to_pc_APPEND;
val _ = checked "code_installed_APPEND_statement" code_installed_APPEND;
val _ = checked "code_installed_isPREFIX_statement" code_installed_isPREFIX;
val _ = checked "loc_to_pc_isPREFIX_statement" loc_to_pc_isPREFIX;
val _ = checked "MAP_prog_to_section_Section_num_statement" (GEN_ALL MAP_prog_to_section_Section_num);
val _ = checked "asm_fetch_aux_SOME_append2_statement" asm_fetch_aux_SOME_append2;
val _ = checked "loc_to_pc_append2_statement" loc_to_pc_append2;
val _ = checked "code_installed_append2_statement" code_installed_append2;
val _ = checked "ALOOKUP_PARTITION_statement" ALOOKUP_PARTITION;
val _ = checked "code_installed_prime_def_statement" code_installed'_def;
val _ = checked "code_installed_prime_cons_label_statement" (GEN_ALL code_installed'_cons_label);
val _ = checked "code_installed_prime_cons_non_label_statement" (GEN_ALL code_installed'_cons_non_label);
val _ = checked "code_installed_prime_simp_statement" (GEN_ALL code_installed'_simp);
val _ = checked "loc_to_pc_skip_section_statement" (GEN_ALL loc_to_pc_skip_section);
val _ = checked "asm_fetch_aux_add_statement" (GEN_ALL asm_fetch_aux_add);
val _ = checked "labs_correct_def_statement" labs_correct_def;
val _ = checked "code_installed_eq_statement" code_installed_eq;
val _ = checked "code_installed_cons_statement" (GEN_ALL code_installed_cons);
val _ = checked "labs_correct_hd_statement" (GEN_ALL labs_correct_hd);
val _ = checked "labels_ok_def_statement" labels_ok_def;
val _ = checked "labels_ok_imp_statement" labels_ok_imp;
val _ = checked "labels_ok_labs_correct_statement" labels_ok_labs_correct;
val _ = checked "labs_correct_append_statement" (GEN_ALL labs_correct_append);
val _ = checked "code_installed_prog_to_section_statement" code_installed_prog_to_section;

(* Local originals (not exported), replayed with their source proofs. *)
val code_installed_get_labels_IMP = Q.prove(
  `!top e n q cs bs pc.
      code_installed pc (append (FST (flatten top e n q cs bs))) c /\
      (l1,l2) ∈ get_labels e ==>
      ?v. loc_to_pc l1 l2 c = SOME v`,
  recInduct flatten_ind \\ rw []
  \\ ntac 2 (pop_assum mp_tac)
  \\ once_rewrite_tac [flatten_def]
  \\ Cases_on `p` \\ fs [get_labels_def] THEN1
   (every_case_tac
    \\ TRY pairarg_tac \\ fs []
    \\ TRY pairarg_tac \\ fs [code_installed_def]
    \\ rw [] \\ res_tac \\ fs []
    \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
    \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
    \\ fs [code_installed_def]
    \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
    \\ fs [code_installed_def])
  \\ every_case_tac \\ fs []
  \\ TRY pairarg_tac \\ fs []
  \\ TRY pairarg_tac \\ fs [code_installed_def]
  \\ TRY pairarg_tac \\ fs [code_installed_def]
  \\ rw [] \\ res_tac \\ fs [code_installed_def]
  \\ fs [get_labels_def]
  \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
  \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []
  \\ imp_res_tac code_installed_append_imp \\ res_tac \\ fs []);
val _ = checked "code_installed_get_labels_IMP_statement" (GEN_ALL code_installed_get_labels_IMP);

val asm_fetch_aux_SOME_append = Q.prove(
  `∀pc code l code2.
  asm_fetch_aux pc code = SOME l ⇒
  asm_fetch_aux pc (code++code2) = SOME l`,
  ho_match_mp_tac asm_fetch_aux_ind>>simp[asm_fetch_aux_def]>>rw[]);
val _ = checked "asm_fetch_aux_SOME_append_statement" asm_fetch_aux_SOME_append;

val asm_fetch_aux_SOME_isPREFIX = Q.prove(
  `∀pc code l code2.
  asm_fetch_aux pc code = SOME l /\
  code ≼ code2 ==>
  asm_fetch_aux pc code2 = SOME l`,
  rw[]>>fs[IS_PREFIX_APPEND]>>
  metis_tac[asm_fetch_aux_SOME_append]);
val _ = checked "asm_fetch_aux_SOME_isPREFIX_statement" asm_fetch_aux_SOME_isPREFIX;

(* First (line 228) declaration of the duplicated local name. *)
val MAP_prog_to_section_FST = Q.prove(
  `MAP (λs. case s of Section n v => n) (MAP prog_to_section prog) =
  MAP FST prog`,
  match_mp_tac LIST_EQ>>rw[EL_MAP]>>Cases_on`EL x prog`>>fs[prog_to_section_def]>>
  pairarg_tac>>fs[]);
val _ = checked "MAP_prog_to_section_FST_statement" (GEN_ALL MAP_prog_to_section_FST);

val code_installed_prog_to_section_lemma = Q.prove(
  `!prog4 n prog3.
      ALOOKUP prog4 n = SOME prog3 ==>
      ?pc.
        code_installed' pc (append (FST (flatten T prog3 n (next_lab prog3 2) [] [])))
          (MAP prog_to_section prog4) /\
        loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc`,
  Induct_on `prog4` \\ fs [] \\ Cases \\ fs [ALOOKUP_def] \\ rw []
  THEN1
   (fs [stack_to_labTheory.prog_to_section_def] \\ pairarg_tac \\ fs []
    \\ once_rewrite_tac [labSemTheory.loc_to_pc_def]
    \\ fs [code_installed'_simp])
  \\ res_tac \\ fs [stack_to_labTheory.prog_to_section_def] \\ pairarg_tac
  \\ fs [loc_to_pc_skip_section,code_installed_cons]);
val _ = checked "code_installed_prog_to_section_lemma_statement" code_installed_prog_to_section_lemma;
