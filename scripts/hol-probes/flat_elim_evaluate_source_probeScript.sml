(* Typed statements of the flat-elimination evaluation simulation lemmas. *)
load "preamble";
load "flat_elimProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble flat_elimProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "evaluate_keep_flat_state_rel_eq_lemma_typed"
  flat_elimProofTheory.evaluate_keep_flat_state_rel_eq_lemma;
val _ = show "evaluate_sing_keep_flat_state_rel_eq_typed"
  flat_elimProofTheory.evaluate_sing_keep_flat_state_rel_eq;
val _ = show "evaluate_dec_flat_state_rel_typed"
  flat_elimProofTheory.evaluate_dec_flat_state_rel;
val _ = show "evaluate_flat_state_rel_lemma_typed"
  flat_elimProofTheory.evaluate_flat_state_rel_lemma;
val _ = show "evaluate_sing_notKeep_flat_state_rel_typed"
  flat_elimProofTheory.evaluate_sing_notKeep_flat_state_rel;
