(* Typed source declarations for bvi_tmc. *)
load "preamble";
load "bvi_tmcTheory";
open HolKernel Parse boolLib bossLib;
open preamble bvi_tmcTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = print ("call_block_typed=" ^
  String.concatWith "; "
    (map (fn c => let val (n,t) = dest_const c in n ^ ":" ^ type_to_string t end)
      [``bvi_tmc$CallBlock``, ``bvi_tmc$RCall``]) ^ "\n");

val _ = show "pure_op_def_typed" bvi_tmcTheory.pure_op_def;
val _ = show "pure_exp_def_typed" bvi_tmcTheory.pure_exp_def;
val _ = show "bind_def_typed" bvi_tmcTheory.bind_def;
val _ = show "shift_vars_def_typed" bvi_tmcTheory.shift_vars_def;
val _ = show "shift_cb_def_typed" bvi_tmcTheory.shift_cb_def;
val _ = show "shift_cb_dist_typed" bvi_tmcTheory.shift_cb_dist;
val _ = show "shift_cb_zero_typed" bvi_tmcTheory.shift_cb_zero;
val _ = show "call_to_cb_def_typed" bvi_tmcTheory.call_to_cb_def;
val _ = show "bvi_to_cb_aux_def_typed" bvi_tmcTheory.bvi_to_cb_aux_def;
val _ = show "wf_vars_def_typed" bvi_tmcTheory.wf_vars_def;
val _ = show "wf_vars_empty_typed" bvi_tmcTheory.wf_vars_empty;
val _ = show "wf_vars_expand_typed" bvi_tmcTheory.wf_vars_expand;
val _ = show "wf_vars_shift_typed" bvi_tmcTheory.wf_vars_shift;
val _ = show "wf_vars_shift_sing_typed" bvi_tmcTheory.wf_vars_shift_sing;
val _ = show "wf_vars_append_typed" bvi_tmcTheory.wf_vars_append;
val _ = show "wf_vars_cons_typed" bvi_tmcTheory.wf_vars_cons;
val _ = show "wf_vars_bind_typed" bvi_tmcTheory.wf_vars_bind;
val _ = show "wf_cb_def_typed" bvi_tmcTheory.wf_cb_def;
val _ = show "wf_cb_expand_typed" bvi_tmcTheory.wf_cb_expand;
val _ = show "wf_cb_shift_sing_typed" bvi_tmcTheory.wf_cb_shift_sing;
val _ = show "bvi_to_cb_aux_sing_typed" bvi_tmcTheory.bvi_to_cb_aux_sing;
val _ = show "bvi_to_cb_aux_wf_inl_typed" bvi_tmcTheory.bvi_to_cb_aux_wf_inl;
val _ = show "bvi_to_cb_aux_wf_inr_typed" bvi_tmcTheory.bvi_to_cb_aux_wf_inr;

(* Local lemmas are not exported by the theory; replay their source statements. *)
val _ = print "bvi_to_cb_aux_wf_inl_lemma_typed=";
val _ = print_term
  ``(∀n loc tag exp bs vs.
       bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INL vs) ⇒
       pure_exps n bs ∧
       wf_vars (LENGTH bs) vs ∧
       small_enough_int (&LENGTH vs)) ∧
     (∀n loc tag args bs vs.
       bvi_to_cb_aux n loc tag args = SOME (bs,INL vs) ⇒
       pure_exps n bs ∧
       wf_vars (LENGTH bs) vs ∧
       small_enough_int (&LENGTH vs))``;
val _ = print "\n";
val _ = print "bvi_to_cb_aux_wf_inr_lemma_typed=";
val _ = print_term
  ``(∀n loc tag exp bs cb.
       bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INR cb) ⇒
       wf_cb (LENGTH bs) cb ∧
       ∃l child r.
         cb = CallBlock tag l child r) ∧
     (∀n loc tag args bs cb.
       bvi_to_cb_aux n loc tag args = SOME (bs,INR cb) ⇒
       wf_cb (LENGTH bs) cb ∧
       ∃l child r.
         cb = CallBlock tag l child r)``;
val _ = print "\n";

val _ = show "bvi_to_cb_def_typed" bvi_tmcTheory.bvi_to_cb_def;
val _ = show "bvi_to_cb_wf_typed" bvi_tmcTheory.bvi_to_cb_wf;
val _ = show "bvi_to_cb_cases_typed" bvi_tmcTheory.bvi_to_cb_cases;
val _ = show "cb_to_bvi_def_typed" bvi_tmcTheory.cb_to_bvi_def;
val _ = show "mut_cons_def_typed" bvi_tmcTheory.mut_cons_def;
val _ = show "fill_hole_def_typed" bvi_tmcTheory.fill_hole_def;
val _ = show "optimise_call_def_typed" bvi_tmcTheory.optimise_call_def;
val _ = show "update_cons_def_typed" bvi_tmcTheory.update_cons_def;
val _ = show "cb_size_def_typed" bvi_tmcTheory.cb_size_def;
val _ = show "cb_to_bvi_worker_aux_def_typed" bvi_tmcTheory.cb_to_bvi_worker_aux_def;
val _ = show "cb_to_bvi_worker_aux_alt_def_typed" bvi_tmcTheory.cb_to_bvi_worker_aux_alt_def;
val _ = show "cb_to_bvi_worker_aux_alt_thm_typed" bvi_tmcTheory.cb_to_bvi_worker_aux_alt_thm;
val _ = show "cb_to_bvi_worker_def_typed" bvi_tmcTheory.cb_to_bvi_worker_def;
val _ = show "cb_to_bvi_wrapper_def_typed" bvi_tmcTheory.cb_to_bvi_wrapper_def;
val _ = show "rewrite_wrapper_def_typed" bvi_tmcTheory.rewrite_wrapper_def;
val _ = show "rewrite_worker_def_typed" bvi_tmcTheory.rewrite_worker_def;
val _ = show "compile_exp_def_typed" bvi_tmcTheory.compile_exp_def;
val _ = show "compile_each_def_typed" bvi_tmcTheory.compile_each_def;
val _ = show "compile_prog_def_typed" bvi_tmcTheory.compile_prog_def;
