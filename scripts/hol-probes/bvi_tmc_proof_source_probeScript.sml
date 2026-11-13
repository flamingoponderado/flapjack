(* Typed source declarations for the bvi_tmcProof script. *)
load "preamble";
load "bvi_tmcProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvi_tmcProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "free_names_def_typed" bvi_tmcProofTheory.free_names_def;
val _ = show "namespace_rel_def_typed" bvi_tmcProofTheory.namespace_rel_def;
val _ = show "input_condition_def_typed" bvi_tmcProofTheory.input_condition_def;
val _ = show "no_mutcons_def_typed" bvi_tmcProofTheory.no_mutcons_def;
val _ = show "no_mutcons_op_def_typed" bvi_tmcProofTheory.no_mutcons_op_def;
val _ = show "code_rel_def_typed" bvi_tmcProofTheory.code_rel_def;
val _ = show "code_rel_cases_typed" bvi_tmcProofTheory.code_rel_cases;
val _ = show "code_rel_domain_typed" bvi_tmcProofTheory.code_rel_domain;
val _ = show "code_rel_union_typed" bvi_tmcProofTheory.code_rel_union;
val _ = show "compile_each_code_rel_typed" bvi_tmcProofTheory.compile_each_code_rel;
val _ = show "compile_each_ALL_DISTINCT_typed" bvi_tmcProofTheory.compile_each_ALL_DISTINCT;
val _ = show "compile_each_LENGTH_typed" bvi_tmcProofTheory.compile_each_LENGTH;
val _ = show "compile_each_MEM_typed" bvi_tmcProofTheory.compile_each_MEM;
val _ = show "compile_each_namespace_rel_typed" bvi_tmcProofTheory.compile_each_namespace_rel;
val _ = show "compile_each_next_mono_typed" bvi_tmcProofTheory.compile_each_next_mono;
val _ = show "compile_prog_ALL_DISTINCT_typed" bvi_tmcProofTheory.compile_prog_ALL_DISTINCT;
val _ = show "compile_prog_MEM_typed" bvi_tmcProofTheory.compile_prog_MEM;
val _ = show "compile_prog_next_mono_typed" bvi_tmcProofTheory.compile_prog_next_mono;
val _ = show "namespace_rel_union_typed" bvi_tmcProofTheory.namespace_rel_union;
val _ = show "optimised_code_def_typed" bvi_tmcProofTheory.optimised_code_def;
val _ = show "list_rel_front_typed" bvi_tmcProofTheory.list_rel_front;
val _ = show "list_rel_last_typed" bvi_tmcProofTheory.list_rel_last;
val _ = show "wrapper_strip_if_else_typed" bvi_tmcProofTheory.wrapper_strip_if_else;
val _ = show "wrapper_strip_if_then_typed" bvi_tmcProofTheory.wrapper_strip_if_then;
val _ = show "wrapper_strip_let_typed" bvi_tmcProofTheory.wrapper_strip_let;
val _ = show "wrapper_strip_tick_typed" bvi_tmcProofTheory.wrapper_strip_tick;

(* Local lemmas are not exported by the theory; replay their source statements. *)
val _ = print "rewrite_wrapper_NONE_irrel_typed=";
val _ = print_term
  ``∀loc lo1 n exp lo2.
      rewrite_wrapper loc lo1 n exp = NONE ⇒
      rewrite_wrapper loc lo2 n exp = NONE``;
val _ = print "\n";
val _ = print "compile_exp_next_addr_typed=";
val _ = print_term
  ``∀loc next args exp.
      compile_exp loc next args exp = NONE ⇒
      compile_exp loc (next + bvl_to_bvi_namespaces) args exp = NONE``;
val _ = print "\n";
val _ = print "compile_exp_SOME_irrel_typed=";
val _ = print_term
  ``∀loc next args exp w.
      compile_exp loc next args exp = SOME w ⇒
      ∀next2. ∃w'. compile_exp loc next2 args exp = SOME w'``;
val _ = print "\n";

val _ = show "compile_each_keeps_names_typed" bvi_tmcProofTheory.compile_each_keeps_names;
val _ = show "compile_prog_keeps_names_typed" bvi_tmcProofTheory.compile_prog_keeps_names;

(* These local results are replayed with their original source proofs. *)
val vars_labels = Q.prove
  (`BIGUNION (set (MAP bviProps$get_code_labels (MAP (λn. bvi$Var n) vs))) = ∅`,
   Induct_on `vs` \\ gvs []);
val _ = show "get_code_labels_MAP_Var_replay_typed" vars_labels;
val worker_aux_labels = Q.prove
  (`∀cb loc_opt ptr idx.
     bviProps$get_code_labels (bvi_tmc$cb_to_bvi_worker_aux cb loc_opt ptr idx) = {loc_opt}`,
   recInduct bvi_tmcTheory.cb_to_bvi_worker_aux_ind
   \\ simp [bvi_tmcTheory.cb_to_bvi_worker_aux_def, bvi_tmcTheory.optimise_call_def,
            bvi_tmcTheory.mut_cons_def, bvi_tmcTheory.update_cons_def,
            closLangTheory.assign_get_code_label_def, vars_labels]);
val _ = show "cb_to_bvi_worker_aux_code_labels_replay_typed" worker_aux_labels;
val worker_labels = Q.prove
  (`bviProps$get_code_labels (bvi_tmc$cb_to_bvi_worker cb loc_opt ptr idx) = {loc_opt}`,
   Cases_on `cb`
   \\ simp [bvi_tmcTheory.cb_to_bvi_worker_def, bvi_tmcTheory.optimise_call_def,
            bvi_tmcTheory.mut_cons_def, bvi_tmcTheory.update_cons_def,
            closLangTheory.assign_get_code_label_def, worker_aux_labels, vars_labels]);
val _ = show "cb_to_bvi_worker_code_labels_replay_typed" worker_labels;
val wrapper_labels = Q.prove
  (`bviProps$get_code_labels (bvi_tmc$cb_to_bvi_wrapper tag left child right loc_opt) = {loc_opt}`,
   simp [bvi_tmcTheory.cb_to_bvi_wrapper_def, bvi_tmcTheory.mut_cons_def,
         bvi_tmcTheory.finalise_cons_def, closLangTheory.assign_get_code_label_def,
         worker_aux_labels, vars_labels]);
val _ = show "cb_to_bvi_wrapper_code_labels_replay_typed" wrapper_labels;
