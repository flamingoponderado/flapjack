(* Typed captures for the PR1213 wordConvsProof rows (review 5978345241 should-fix 7)
   that had no typed capture. Exported theorems are printed with show_types from the
   loaded wordConvsProofTheory. [local] theorems are not exported: each statement is
   read literally from the pinned source (between its `Theorem name[...]:` or
   `Triviality name:` header and `Proof`) and parsed with show_types in the loaded
   wordConvsProofTheory context (a typed source parse, not re-proved). The one
   `Theorem x[local] = <ML>` alias, const_fp_loop_Seq, is replayed from its literal,
   source-guarded derivation and its conclusion printed with show_types. *)
load "preamble"; load "wordConvsProofTheory";
open HolKernel Parse boolLib bossLib preamble
  wordLangTheory word_to_wordTheory wordConvsTheory word_simpTheory word_allocTheory
  word_instTheory word_unreachTheory word_removeTheory word_cseTheory word_elimTheory
  word_copyTheory wordConvsProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = show_types := true;
val source_cake = case OS.Process.getEnv "CAKEML" of
    SOME p => p
  | NONE => (case OS.Process.getEnv "FLAPJACK_HOL_PROBE_DIR" of
      SOME p => OS.Path.concat (OS.Path.dir (OS.Path.dir p), "cakeml")
    | NONE => raise Fail "CAKEML or FLAPJACK_HOL_PROBE_DIR is required");
val source_stream = TextIO.openIn
  (OS.Path.concat (source_cake, "compiler/backend/proofs/wordConvsProofScript.sml"));
val source_text = TextIO.inputAll source_stream;
val _ = TextIO.closeIn source_stream;
fun guard name lit = if String.isSubstring lit source_text then ()
  else raise Fail (name ^ " literal source changed");
fun after_prefix pre s =
  case (Substring.position pre (Substring.full s)) of
    (_, rest) => if Substring.isEmpty rest then NONE
                 else SOME (Substring.string (Substring.triml (String.size pre) rest));
fun statement_of name =
  let
    fun first [] = raise Fail ("missing " ^ name)
      | first (h :: t) = (case after_prefix h source_text of SOME r => r | NONE => first t)
    val rest = first ["\nTheorem " ^ name ^ "[", "\nTheorem  " ^ name ^ "[",
                      "\nTriviality " ^ name, "\nTriviality  " ^ name]
    val body = case after_prefix ":\n" rest of SOME b => b | NONE => raise Fail ("no statement " ^ name)
    val (stmt, _) = Substring.position "\nProof" (Substring.full body)
  in Substring.string stmt end;
fun capture label name =
  let val tm = Parse.Term [QUOTE (statement_of name)]
  in (print (label ^ "="); print_term tm; print "\n") end;
fun capture_thm label th = (print (label ^ "="); print_term (concl th); print "\n");
val _ = capture "ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma_source_statement_typed" "ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma";
val _ = capture "ALL_DISTINCT_extract_labels_remove_unreach_source_statement_typed" "ALL_DISTINCT_extract_labels_remove_unreach";
val _ = capture "MEM_extract_labels_Seq_assoc_right_lemma_source_statement_typed" "MEM_extract_labels_Seq_assoc_right_lemma";
val _ = capture "Seq_assoc_no_inst_source_statement_typed" "Seq_assoc_no_inst";
val _ = capture "Seq_assoc_right_not_created_subprogs_source_statement_typed" "Seq_assoc_right_not_created_subprogs";
val _ = capture "SimpSeq_not_created_subprogs_source_statement_typed" "SimpSeq_not_created_subprogs";
val _ = capture_thm "compile_exp_no_inst_statement" compile_exp_no_inst;
val _ = capture "compile_exp_not_created_subprogs_source_statement_typed" "compile_exp_not_created_subprogs";
val _ = capture_thm "compile_single_not_created_subprogs_statement" compile_single_not_created_subprogs;
val _ = guard "const_fp_loop_Seq" "Theorem const_fp_loop_Seq[local] =\n  const_fp_loop_def |> BODY_CONJUNCTS\n  |> filter (can (find_term (fn t => total (fst o dest_const) t = SOME \"Seq\")) o concl)\n  |> LIST_CONJ";
val _ = capture_thm "const_fp_loop_Seq_replay_statement_typed" (const_fp_loop_def |> BODY_CONJUNCTS |> filter (can (find_term (fn t => total (fst o dest_const) t = SOME "Seq")) o concl) |> LIST_CONJ);
val _ = capture "const_fp_loop_dummy_cases_source_statement_typed" "const_fp_loop_dummy_cases";
val _ = capture "dest_If_thm_source_statement_typed" "dest_If_thm";
val _ = capture "dest_Seq_no_inst_source_statement_typed" "dest_Seq_no_inst";
val _ = capture "every_inst_SmartSeq_source_statement_typed" "every_inst_SmartSeq";
val _ = capture "every_inst_const_fp_source_statement_typed" "every_inst_const_fp";
val _ = capture "every_inst_drop_consts_source_statement_typed" "every_inst_drop_consts";
val _ = capture "extract_labels_Seq_assoc_source_statement_typed" "extract_labels_Seq_assoc";
val _ = capture "extract_labels_Seq_assoc_lemma_source_statement_typed" "extract_labels_Seq_assoc_lemma";
val _ = capture "extract_labels_Seq_assoc_right_lemma_source_statement_typed" "extract_labels_Seq_assoc_right_lemma";
val _ = capture "extract_labels_SimpSeq_source_statement_typed" "extract_labels_SimpSeq";
val _ = capture "extract_labels_SmartSeq_source_statement_typed" "extract_labels_SmartSeq";
val _ = capture_thm "extract_labels_compile_exp_statement" extract_labels_compile_exp;
val _ = capture "extract_labels_const_fp_source_statement_typed" "extract_labels_const_fp";
val _ = capture "extract_labels_const_fp_loop_source_statement_typed" "extract_labels_const_fp_loop";
val _ = capture "extract_labels_drop_consts_source_statement_typed" "extract_labels_drop_consts";
val _ = capture "extract_labels_drop_consts_1_source_statement_typed" "extract_labels_drop_consts_1";
val _ = capture "extract_labels_remove_unreach_source_statement_typed" "extract_labels_remove_unreach";
val _ = capture_thm "extract_labels_word_common_subexp_elim_statement" extract_labels_word_common_subexp_elim;
val _ = capture "fake_moves_not_created_subprogs_source_statement_typed" "fake_moves_not_created_subprogs";
val _ = capture "fake_moves_wf_cutsets_source_statement_typed" "fake_moves_wf_cutsets";
val _ = capture "fake_seq_not_created_subprogs_source_statement_typed" "fake_seq_not_created_subprogs";
val _ = capture "fake_seq_wf_cutsets_source_statement_typed" "fake_seq_wf_cutsets";
val _ = capture_thm "flat_exp_conventions_word_common_subexp_elim_statement" flat_exp_conventions_word_common_subexp_elim;
val _ = capture "full_ssa_cc_trans_not_created_subprogs_source_statement_typed" "full_ssa_cc_trans_not_created_subprogs";
val _ = capture_thm "full_ssa_cc_trans_wf_cutsets_statement" full_ssa_cc_trans_wf_cutsets;
val _ = capture "inst_select_exp_not_created_subprogs_source_statement_typed" "inst_select_exp_not_created_subprogs";
val _ = capture "inst_select_not_created_subprogs_source_statement_typed" "inst_select_not_created_subprogs";
val _ = capture "labels_rel_append_imp_source_statement_typed" "labels_rel_append_imp";
val _ = capture "labels_rel_hoist2_source_statement_typed" "labels_rel_hoist2";
val _ = capture "labels_rel_push_out_if_source_statement_typed" "labels_rel_push_out_if";
val _ = capture_thm "labels_rel_remove_unreach_statement" labels_rel_remove_unreach;
val _ = capture "labels_rel_simp_duplicate_if_source_statement_typed" "labels_rel_simp_duplicate_if";
val _ = capture "loop_setup_not_created_subprogs_source_statement_typed" "loop_setup_not_created_subprogs";
val _ = capture "loop_setup_wf_cutsets_source_statement_typed" "loop_setup_wf_cutsets";
val _ = capture "not_created_subprogs_Seq_assoc_source_statement_typed" "not_created_subprogs_Seq_assoc";
val _ = capture "not_created_subprogs_SmartSeq_source_statement_typed" "not_created_subprogs_SmartSeq";
val _ = capture "not_created_subprogs_const_fp_source_statement_typed" "not_created_subprogs_const_fp";
val _ = capture "not_created_subprogs_const_fp_loop_source_statement_typed" "not_created_subprogs_const_fp_loop";
val _ = capture "not_created_subprogs_drop_consts_source_statement_typed" "not_created_subprogs_drop_consts";
val _ = capture "not_created_subprogs_hoist2_source_statement_typed" "not_created_subprogs_hoist2";
val _ = capture "not_created_subprogs_push_out_if_source_statement_typed" "not_created_subprogs_push_out_if";
val _ = capture "not_created_subprogs_simp_duplicate_if_source_statement_typed" "not_created_subprogs_simp_duplicate_if";
val _ = capture "remove_unreach_not_created_subprogs_source_statement_typed" "remove_unreach_not_created_subprogs";
val _ = capture "setup_ssa_not_created_subprogs_source_statement_typed" "setup_ssa_not_created_subprogs";
val _ = capture "simp_duplicate_if_no_inst_source_statement_typed" "simp_duplicate_if_no_inst";
val _ = capture "simp_push_out_if_no_inst_source_statement_typed" "simp_push_out_if_no_inst";
val _ = capture "ssa_cc_trans_inst_not_created_subprogs_source_statement_typed" "ssa_cc_trans_inst_not_created_subprogs";
val _ = capture "ssa_cc_trans_not_created_subprogs_source_statement_typed" "ssa_cc_trans_not_created_subprogs";
val _ = capture "ssa_cc_trans_wf_cutsets_source_statement_typed" "ssa_cc_trans_wf_cutsets";
val _ = capture "ssa_reconcile_wf_cutsets_source_statement_typed" "ssa_reconcile_wf_cutsets";
val _ = capture "three_to_two_reg_prog_not_created_subprogs_source_statement_typed" "three_to_two_reg_prog_not_created_subprogs";
val _ = capture_thm "three_to_two_reg_prog_wf_cutsets_statement" three_to_two_reg_prog_wf_cutsets;
val _ = capture "try_if_hoist2_no_inst_source_statement_typed" "try_if_hoist2_no_inst";
val _ = capture "wf_cutsets_Seq_assoc_right_lemma_source_statement_typed" "wf_cutsets_Seq_assoc_right_lemma";
val _ = capture "wf_cutsets_SimpSeq_source_statement_typed" "wf_cutsets_SimpSeq";
val _ = capture_thm "wf_cutsets_remove_unreach_statement" wf_cutsets_remove_unreach;
val _ = capture_thm "wf_cutsets_word_common_subexp_elim_statement" wf_cutsets_word_common_subexp_elim;
val _ = capture "word_common_subexp_elim_not_created_subprogs_source_statement_typed" "word_common_subexp_elim_not_created_subprogs";
val _ = capture "word_cseInst_not_created_subprogs_source_statement_typed" "word_cseInst_not_created_subprogs";
val _ = capture "word_cse_extract_labels_source_statement_typed" "word_cse_extract_labels";
val _ = capture "word_cse_flat_exp_conventions_source_statement_typed" "word_cse_flat_exp_conventions";
val _ = capture "word_cse_get_code_labels_source_statement_typed" "word_cse_get_code_labels";
val _ = capture "word_cse_not_created_subprogs_source_statement_typed" "word_cse_not_created_subprogs";
val _ = capture "word_cse_wf_cutsets_source_statement_typed" "word_cse_wf_cutsets";
val _ = capture "word_get_code_labels_word_common_subexp_elim_source_statement_typed" "word_get_code_labels_word_common_subexp_elim";
val _ = capture "word_good_handlers_Seq_assoc_source_statement_typed" "word_good_handlers_Seq_assoc";
val _ = capture "word_good_handlers_Seq_assoc_right_source_statement_typed" "word_good_handlers_Seq_assoc_right";
val _ = capture "word_good_handlers_SimpSeq_source_statement_typed" "word_good_handlers_SimpSeq";
val _ = capture "word_good_handlers_SmartSeq_source_statement_typed" "word_good_handlers_SmartSeq";
val _ = capture "word_good_handlers_const_fp_loop_source_statement_typed" "word_good_handlers_const_fp_loop";
val _ = capture "word_good_handlers_drop_consts_source_statement_typed" "word_good_handlers_drop_consts";
val _ = capture "word_good_handlers_fake_moves_source_statement_typed" "word_good_handlers_fake_moves";
val _ = capture "word_good_handlers_full_ssa_cc_trans_source_statement_typed" "word_good_handlers_full_ssa_cc_trans";
val _ = capture "word_good_handlers_inst_select_source_statement_typed" "word_good_handlers_inst_select";
val _ = capture "word_good_handlers_inst_select_exp_source_statement_typed" "word_good_handlers_inst_select_exp";
val _ = capture "word_good_handlers_remove_unreach_source_statement_typed" "word_good_handlers_remove_unreach";
val _ = capture "word_good_handlers_simp_duplicate_if_source_statement_typed" "word_good_handlers_simp_duplicate_if";
val _ = capture "word_good_handlers_simp_push_out_if_source_statement_typed" "word_good_handlers_simp_push_out_if";
val _ = capture "word_good_handlers_ssa_cc_trans_source_statement_typed" "word_good_handlers_ssa_cc_trans";
val _ = capture "word_good_handlers_three_to_two_reg_prog_source_statement_typed" "word_good_handlers_three_to_two_reg_prog";
val _ = capture "word_good_handlers_try_if_hoist2_source_statement_typed" "word_good_handlers_try_if_hoist2";
val _ = capture "word_good_handlers_word_common_subexp_elim_source_statement_typed" "word_good_handlers_word_common_subexp_elim";
val _ = capture "word_good_handlers_word_simp_source_statement_typed" "word_good_handlers_word_simp";
val _ = capture_thm "word_good_handlers_word_to_word_statement" word_good_handlers_word_to_word;
val _ = capture_thm "word_good_handlers_word_to_word_incr_statement" word_good_handlers_word_to_word_incr;
val _ = capture "word_good_handlers_word_to_word_incr_helper_source_statement_typed" "word_good_handlers_word_to_word_incr_helper";
val _ = capture "fake_seq_good_handlers_source_statement_typed" "fake_seq_good_handlers";
val _ = capture "ssa_reconcile_good_handlers_source_statement_typed" "ssa_reconcile_good_handlers";
val _ = capture "loop_setup_good_handlers_source_statement_typed" "loop_setup_good_handlers";
