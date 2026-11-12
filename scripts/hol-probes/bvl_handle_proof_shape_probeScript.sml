(* Typed source theorems for the variable-bound and handler-shape lemmas in
   cakeml/compiler/backend/proofs/bvl_handleProofScript.sml. *)
load "bvl_handleProofTheory";
open HolKernel Parse boolLib bossLib;
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
val _ = show "bVarBound_MEM_typed" bvl_handleProofTheory.bVarBound_MEM;
val _ = show "bVarBound_LESS_EQ_typed" bvl_handleProofTheory.bVarBound_LESS_EQ;
val _ = show "bVarBound_LetLet_typed" bvl_handleProofTheory.bVarBound_LetLet;
