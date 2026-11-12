(* Typed source theorems for the variable-bound and handler-shape lemmas in
   cakeml/compiler/backend/proofs/bvl_handleProofScript.sml. *)
load "bvl_handleProofTheory";
load "preamble";
open HolKernel Parse boolLib bossLib;
open preamble bvl_handleTheory bvlPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "IS_SOME_lookup_db_to_set_typed" bvl_handleProofTheory.IS_SOME_lookup_db_to_set;
val _ = show "handle_ok_SmartLet_typed" bvl_handleProofTheory.handle_ok_SmartLet;
val _ = show "can_raise_thm_typed" bvl_handleProofTheory.can_raise_thm;
val _ = show "handle_adj_vars_0_typed" bvl_handleProofTheory.handle_adj_vars_0;
val _ = show "evaluate_handle_adj_vars_lemma_typed" bvl_handleProofTheory.evaluate_handle_adj_vars_lemma;
val _ = show "evaluate_handle_adj_vars_typed" bvl_handleProofTheory.evaluate_handle_adj_vars;
val _ = show "handle_adj_vars_evaluate_typed" bvl_handleProofTheory.handle_adj_vars_evaluate;
val _ = show "evaluate_handle_simp_typed" bvl_handleProofTheory.evaluate_handle_simp;
val _ = show "compile_correct_typed" bvl_handleProofTheory.compile_correct;
val _ = show "compile_any_correct_typed" bvl_handleProofTheory.compile_any_correct;
val _ = show "compile_seqs_correct_typed" bvl_handleProofTheory.compile_seqs_correct;
(* This theorem is local in the original script, so replay its original proof. *)
val get_code_labels_handle_adj_vars_replay = Q.prove (
  `(∀x d l. get_code_labels (handle_adj_vars d l x) = get_code_labels x) ∧
   (∀x d l. MAP get_code_labels (handle_adj_vars1 d l x) = MAP get_code_labels x)`,
  Induct \\ fs [handle_adj_vars_def]);
val _ = show "get_code_labels_handle_adj_vars_replay" get_code_labels_handle_adj_vars_replay;
val get_code_labels_dest_handle_Raise_replay = Q.prove (
  `∀c x. dest_handle_Raise c = SOME x ⇒ get_code_labels c = get_code_labels x`,
  ho_match_mp_tac dest_handle_Raise_ind \\ rpt strip_tac \\ gvs [dest_handle_Raise_def,AllCaseEqs()]);
val _ = show "get_code_labels_dest_handle_Raise_replay" get_code_labels_dest_handle_Raise_replay;
val _ = show "LetLet_code_labels_typed" bvl_handleProofTheory.LetLet_code_labels;
val _ = show "handle_ok_EVERY_typed" bvl_handleProofTheory.handle_ok_EVERY;
val _ = show "compile_handle_ok_typed" bvl_handleProofTheory.compile_handle_ok;
val _ = show "compile_exp_handle_ok_typed" bvl_handleProofTheory.compile_exp_handle_ok;
val _ = show "compile_seqs_handle_ok_typed" bvl_handleProofTheory.compile_seqs_handle_ok;
val _ = show "compile_any_handle_ok_typed" bvl_handleProofTheory.compile_any_handle_ok;
val _ = show "bVarBound_compile_typed" bvl_handleProofTheory.bVarBound_compile;
val _ = show "compile_exp_bVarBound_typed" bvl_handleProofTheory.compile_exp_bVarBound;
val _ = show "compile_seqs_bVarBound_typed" bvl_handleProofTheory.compile_seqs_bVarBound;
val _ = show "bVarBound_OptionalLetLet_typed" bvl_handleProofTheory.bVarBound_OptionalLetLet;
val _ = show "compile_IMP_bVarBound_typed" bvl_handleProofTheory.compile_IMP_bVarBound;
val _ = show "handle_ok_OptionalLetLet_typed" bvl_handleProofTheory.handle_ok_OptionalLetLet;
val _ = show "handle_ok_Var_Const_list_typed" bvl_handleProofTheory.handle_ok_Var_Const_list;
val _ = show "compile_length_typed" bvl_handleTheory.compile_length;
val _ = show "compile_IMP_LENGTH_typed" bvl_handleProofTheory.compile_IMP_LENGTH;
val _ = show "compile_code_labels_typed" bvl_handleProofTheory.compile_code_labels;
val _ = show "get_code_labels_handle_simp_typed" bvl_handleProofTheory.get_code_labels_handle_simp;
val _ = show "compile_exp_code_labels_typed" bvl_handleProofTheory.compile_exp_code_labels;
val _ = show "compile_seqs_code_labels_typed" bvl_handleProofTheory.compile_seqs_code_labels;
val _ = show "bVarBound_MEM_typed" bvl_handleProofTheory.bVarBound_MEM;
val _ = show "bVarBound_LESS_EQ_typed" bvl_handleProofTheory.bVarBound_LESS_EQ;
val _ = show "bVarBound_LetLet_typed" bvl_handleProofTheory.bVarBound_LetLet;
