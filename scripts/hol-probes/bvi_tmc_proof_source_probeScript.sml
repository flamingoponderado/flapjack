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
val _ = show "fmap_inj_def_typed" bvi_tmcProofTheory.fmap_inj_def;
val _ = show "fmap_inj_update_typed" bvi_tmcProofTheory.fmap_inj_update;
val _ = show "v_rel_rules_typed" bvi_tmcProofTheory.v_rel_rules;
val _ = show "ref_rel_rules_typed" bvi_tmcProofTheory.ref_rel_rules;
val _ = show "env_rel_def_typed" bvi_tmcProofTheory.env_rel_def;
val _ = show "state_ref_rel_def_typed" bvi_tmcProofTheory.state_ref_rel_def;
val _ = show "state_ref_rel_filled_typed" bvi_tmcProofTheory.state_ref_rel_filled;
val _ = show "state_rel_def_typed" bvi_tmcProofTheory.state_rel_def;
val _ = show "state_rel_filled_typed" bvi_tmcProofTheory.state_rel_filled;
val _ = show "hole_has_val_def_typed" bvi_tmcProofTheory.hole_has_val_def;
val _ = show "holes_unchanged_except_def_typed" bvi_tmcProofTheory.holes_unchanged_except_def;
val _ = show "holes_unchanged_except_refl_typed" bvi_tmcProofTheory.holes_unchanged_except_refl;
val _ = show "holes_unchanged_except_submap_typed" bvi_tmcProofTheory.holes_unchanged_except_submap;
val _ = show "holes_unchanged_except_subset_typed" bvi_tmcProofTheory.holes_unchanged_except_subset;
val _ = show "holes_unchanged_except_del_typed" bvi_tmcProofTheory.holes_unchanged_except_del;
val _ = show "holes_unchanged_except_del_SING_typed" bvi_tmcProofTheory.holes_unchanged_except_del_SING;
val _ = show "holes_unchanged_except_changed_typed" bvi_tmcProofTheory.holes_unchanged_except_changed;
val _ = show "holes_unchanged_except_filled_typed" bvi_tmcProofTheory.holes_unchanged_except_filled;
val _ = show "unchanged_hole_has_val_typed" bvi_tmcProofTheory.unchanged_hole_has_val;
val _ = show "hole_has_val_append_typed" bvi_tmcProofTheory.hole_has_val_append;
val _ = show "hole_has_val_unappend_typed" bvi_tmcProofTheory.hole_has_val_unappend;
val _ = show "hole_has_val_dec_typed" bvi_tmcProofTheory.hole_has_val_dec;
val _ = show "only_fresh_refl_typed" bvi_tmcProofTheory.only_fresh_refl;
val _ = show "only_fresh_trans_typed" bvi_tmcProofTheory.only_fresh_trans;
val _ = show "only_fresh_submap_typed" bvi_tmcProofTheory.only_fresh_submap;
val _ = show "non_fresh_not_in_frange_typed" bvi_tmcProofTheory.non_fresh_not_in_frange;
val _ = show "fresh_ptr_fresh_typed" bvi_tmcProofTheory.fresh_ptr_fresh;
val _ = show "fresh_not_in_range_f_typed" bvi_tmcProofTheory.fresh_not_in_range_f;
val _ = show "only_fresh_del_typed" bvi_tmcProofTheory.only_fresh_del;
val _ = show "flookup_com_neq_typed" bvi_tmcProofTheory.flookup_com_neq;
val _ = show "mb_rel_def_typed" bvi_tmcProofTheory.mb_rel_def;
val _ = show "mb_rel_cons_typed" bvi_tmcProofTheory.mb_rel_cons;
val _ = show "mb_rel_del_typed" bvi_tmcProofTheory.mb_rel_del;
val _ = show "state_ref_rel_update_typed" bvi_tmcProofTheory.state_ref_rel_update;
val _ = show "bvl_to_bvi_refs_typed" bvi_tmcProofTheory.bvl_to_bvi_refs;
val _ = show "holes_unchanged_except_frange_update_typed" bvi_tmcProofTheory.holes_unchanged_except_frange_update;
val _ = show "holes_still_not_finalised_frange_update_typed" bvi_tmcProofTheory.holes_still_not_finalised_frange_update;
val _ = show "state_ref_rel_alloc_typed" bvi_tmcProofTheory.state_ref_rel_alloc;
val _ = show "state_rel_alloc_typed" bvi_tmcProofTheory.state_rel_alloc;
val _ = show "state_ref_rel_lookup_typed" bvi_tmcProofTheory.state_ref_rel_lookup;
val _ = show "fmap_inj_flookup_eq_typed" bvi_tmcProofTheory.fmap_inj_flookup_eq;
val _ = show "v_to_list_v_rel_typed" bvi_tmcProofTheory.v_to_list_v_rel;
val _ = show "list_to_v_v_rel_typed" bvi_tmcProofTheory.list_to_v_v_rel;
val _ = show "do_eq_v_rel_typed" bvi_tmcProofTheory.do_eq_v_rel;
val _ = show "do_word_app_v_rel_typed" bvi_tmcProofTheory.do_word_app_v_rel;
val _ = show "do_word_app_v_rel_refl_typed" bvi_tmcProofTheory.do_word_app_v_rel_refl;
val _ = show "no_mutblock_typed" bvi_tmcProofTheory.no_mutblock;
val _ = show "v_to_bytes_v_rel_typed" bvi_tmcProofTheory.v_to_bytes_v_rel;
val _ = show "v_to_words_v_rel_typed" bvi_tmcProofTheory.v_to_words_v_rel;
val _ = show "do_build_v_rel_typed" bvi_tmcProofTheory.do_build_v_rel;
val _ = show "do_build_const_v_rel_typed" bvi_tmcProofTheory.do_build_const_v_rel;
val _ = show "do_app_op_rel_typed" bvi_tmcProofTheory.do_app_op_rel;
val _ = show "do_app_op_finalise_rel_typed" bvi_tmcProofTheory.do_app_op_finalise_rel;
val _ = show "dest_thunk_not_thunk_rel_typed" bvi_tmcProofTheory.dest_thunk_not_thunk_rel;
val _ = show "do_app_op_err_rel_typed" bvi_tmcProofTheory.do_app_op_err_rel;
val _ = show "bvi_to_bvl_refs_typed" bvi_tmcProofTheory.bvi_to_bvl_refs;
val _ = show "finalise_cons_refs_SUBSET_typed" bvi_tmcProofTheory.finalise_cons_refs_SUBSET;
val _ = show "do_app_refs_SUBSET_typed" bvi_tmcProofTheory.do_app_refs_SUBSET;
val _ = show "evaluate_refs_SUBSET_typed" bvi_tmcProofTheory.evaluate_refs_SUBSET;
val _ = show "list_rel_reverse_typed" bvi_tmcProofTheory.list_rel_reverse;
val _ = show "evaluate_fill_hole_typed" bvi_tmcProofTheory.evaluate_fill_hole;
val _ = show "evaluate_fill_hole_val_typed" bvi_tmcProofTheory.evaluate_fill_hole_val;
val _ = show "evaluate_vars_source_typed" bvi_tmcProofTheory.evaluate_vars_source;
val _ = show "evaluate_vars_target_typed" bvi_tmcProofTheory.evaluate_vars_target;
val _ = show "evaluate_vars_expand_env_typed" bvi_tmcProofTheory.evaluate_vars_expand_env;
val _ = show "evaluate_var_list_typed" bvi_tmcProofTheory.evaluate_var_list;
val _ = show "evaluate_var_list_binders_typed" bvi_tmcProofTheory.evaluate_var_list_binders;
val _ = show "evaluate_binders_typed" bvi_tmcProofTheory.evaluate_binders;
val _ = show "evaluate_shift_vars_typed" bvi_tmcProofTheory.evaluate_shift_vars;
val _ = show "evaluate_shift_vars_sing_typed" bvi_tmcProofTheory.evaluate_shift_vars_sing;
val _ = show "evaluate_shift_cb_typed" bvi_tmcProofTheory.evaluate_shift_cb;
val _ = show "evaluate_shift_cb_sing_typed" bvi_tmcProofTheory.evaluate_shift_cb_sing;
(* Replay the original local theorem statement and proof; show rejects hypotheses. *)
open bvi_tmcTheory bviPropsTheory bviSemTheory;
val pure_local_replay = Q.prove (
`(∀e n.
     pure_exp n e ⇒
     ∀env.
       n ≤ LENGTH env ⇒
       ∃v. ∀(s:('c,'ffi) bviSem$state). evaluate ([e],env,s) = (Rval v,s)) ∧
  (∀(x:bvi$exp option). T) ∧
  (∀xs n.
     pure_exps n xs ⇒
     ∀env.
       n ≤ LENGTH env ⇒
       ∃v. ∀(s:('c,'ffi) bviSem$state). evaluate (xs,env,s) = (Rval v,s))`,
ho_match_mp_tac bviTheory.exp_induction
  >> rw []
  >> gvs [pure_exp_def, evaluate_def]
  >- (* Let *)
   (qpat_x_assum ‘∀n. pure_exps n xs ⇒ _’ drule >> strip_tac
    >> first_x_assum drule >> strip_tac >> gvs []
    >> qpat_x_assum ‘∀n. pure_exp n e ⇒ _’ drule >> strip_tac
    >> first_x_assum irule >> gvs [])
  >- (* Op *)
   (qpat_x_assum ‘∀n. pure_exps n xs ⇒ _’ drule >> strip_tac
    >> first_x_assum drule >> strip_tac >> gvs []
    >> Cases_on ‘x’ >> gvs [pure_op_def, do_app_def, do_app_aux_def]
    >- (* IntOp *)
     (Cases_on ‘i’ >> Cases_on ‘xs’ >> gvs [pure_op_def, evaluate_def])
    (* BlockOp *)
    >> Cases_on ‘b’ >> gvs [pure_op_def, do_app_def, do_app_aux_def, bvl_to_bvi_id])
  (* cons *)
  >> once_rewrite_tac [evaluate_CONS]
  >> qpat_x_assum ‘∀n. pure_exp n e ⇒ _’ drule >> strip_tac
  >> first_x_assum drule >> strip_tac >> gvs []
  >> qpat_x_assum ‘∀n. pure_exps n xs ⇒ _’ drule >> strip_tac
  >> first_x_assum drule >> strip_tac >> gvs []);
val _ = show "evaluate_pure_exp_lemma_replay_typed" pure_local_replay;
val _ = show "evaluate_pure_exps_typed" bvi_tmcProofTheory.evaluate_pure_exps;
(* Replay the original local extraction theorem and its proof. *)
val inl_local_replay = Q.prove (
`(∀n loc tag exp bs vs.
     bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INL vs) ⇒
     bs = [exp] ∧
     ∀env.
       n ≤ LENGTH env ⇒
       ∃v.
         ∀(s:('c,'ffi) bviSem$state).
           evaluate ([exp],env,s) = (Rval v,s) ∧
           evaluate (MAP (λn. Var n) vs,v,s) = (Rval v,s)) ∧
  (∀n loc tag args bs vs.
     bvi_to_cb_aux n loc tag args = SOME (bs,INL vs) ⇒
     bs = args ∧
     ∀env.
       n ≤ LENGTH env ⇒
       ∃v.
         ∀(s:('c,'ffi) bviSem$state).
           evaluate (args,env,s) = (Rval v,s) ∧
           evaluate (MAP (λn. Var n) vs,v,s) = (Rval v,s))`,
ho_match_mp_tac bvi_to_cb_aux_ind >> rw [bvi_to_cb_aux_def, call_to_cb_def] >> gvs [evaluate_def]
  >- gvs [CaseEq "prod", CaseEq "option", CaseEq "sum"]
  >- gvs [CaseEq "prod", CaseEq "option", CaseEq "sum"]
  >- gvs [CaseEq "option", CaseEq "prod", CaseEq "sum", evaluate_def]
  >-
   (gvs [AllCaseEqs()]
    >> ‘pure_exps n [Op op args]’ by gvs [pure_exp_def]
    >> ‘∃w. ∀(s:('c,'ffi) bviSem$state). evaluate ([Op op args],env,s) = (Rval w,s)’
         by metis_tac [evaluate_pure_exps]
    >> qexists ‘w’
    >> gen_tac
    >> first_assum $ qspec_then ‘s’ assume_tac
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [evaluate_def, AllCaseEqs()])
  >- gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >- gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >- (rename1 ‘pure_exp n (Var k)’
      >> gvs [pure_exp_def] >> qexists ‘[env❲k❳]’ >> gvs [])
  >- gvs [pure_exp_def]
  >-
   (rename1 ‘pure_exp n (Let es e)’
    >> ‘pure_exps n [Let es e]’ by gvs [pure_exp_def]
    >> ‘∃w. ∀(s:('c,'ffi) bviSem$state). evaluate ([Let es e],env,s) = (Rval w,s)’
         by metis_tac [evaluate_pure_exps]
    >> qexists ‘w’
    >> gen_tac
    >> first_assum $ qspec_then ‘s’ assume_tac
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [evaluate_def])
  >- gvs [pure_exp_def]
  >- gvs [pure_exp_def]
  >- gvs [pure_exp_def]
  >- gvs [pure_exp_def]
  >- gvs [pure_exp_def]
  >-
   (gvs [CaseEq "option"]
    >> gvs [CaseEq "prod"]
    >> reverse $ gvs [CaseEq "sum"]
    >- (Cases_on ‘cb’ >> gvs [shift_cb_def])
    >> gvs [CaseEq "option"]
    >> gvs [CaseEq "prod"]
    >> gvs [CaseEq "sum"]
    >> gvs [CaseEq "call_block"]
    >> gvs [CaseEq "list"])
  >> gvs [CaseEq "option"]
  >> gvs [CaseEq "prod"]
  >> reverse $ gvs [CaseEq "sum"]
  >- (Cases_on ‘cb’ >> gvs [shift_cb_def])
  >> gvs [CaseEq "option"]
  >> gvs [CaseEq "prod"]
  >> gvs [CaseEq "sum"]
  >> gvs [CaseEq "call_block"]
  >> gvs [CaseEq "list"]
  >> last_x_assum drule
  >> strip_tac
  >> gvs []
  >> first_x_assum drule
  >> strip_tac
  >> qexists ‘v ++ v'’
  >> gen_tac
  >> rpt $ first_x_assum $ qspec_then ‘s’ assume_tac
  >> gvs []
  >> imp_res_tac evaluate_SING_IMP
  >> gvs [evaluate_APPEND, evaluate_shift_vars_sing]
  >> imp_res_tac evaluate_vars_expand_env
  >> pop_assum $ qspec_then ‘v'’ mp_tac
  >> strip_tac
  >> gvs [APPEND]);
val _ = show "evaluate_bvi_to_cb_aux_inl_lemma_replay_typed" inl_local_replay;
val _ = show "evaluate_bvi_to_cb_aux_inl_typed" bvi_tmcProofTheory.evaluate_bvi_to_cb_aux_inl;
(* Replay the original local recursive-call extraction theorem and proof. *)
val inr_local_replay = Q.prove (
`(∀n loc tag exp env s t r bs cb.
     bvi_to_cb_aux_sing n loc tag exp = SOME (bs,INR cb) ∧
     evaluate ([Op (BlockOp (Cons tag)) [exp]],env,
               (s:('c,'ffi) bviSem$state)) = (r,t) ∧
     n ≤ LENGTH env ⇒
     ∃as u.
       evaluate (bs,env,s) = (as,u) ∧
       (∀vs.
          as = Rval vs ⇒
          evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) ∧
          ∀extras.
            evaluate ([cb_to_bvi loc cb],vs ++ extras,u) = (r,t)) ∧
       (∀e.
          as = Rerr e ⇒
          (as,u) = (r,t))) ∧
  (∀n loc tag args env s t r bs cb.
     bvi_to_cb_aux n loc tag args = SOME (bs,INR cb) ∧
     evaluate ([Op (BlockOp (Cons tag)) args],env,
               (s:('c,'ffi) bviSem$state)) = (r,t) ∧
     n ≤ LENGTH env ⇒
     ∃as u.
       evaluate (bs,env,s) = (as,u) ∧
       (∀vs.
          as = Rval vs ⇒
          evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) ∧
          ∀extras.
            evaluate ([cb_to_bvi loc cb],vs ++ extras,u) = (r,t)) ∧
       (∀e.
          as = Rerr e ⇒
          (as,u) = (r,t)))`,
ho_match_mp_tac bvi_to_cb_aux_ind
  >> rw []
  >> imp_res_tac bvi_to_cb_aux_wf_inr
  >> gvs []
  >- (* call *)
   (gvs [bvi_to_cb_aux_def, call_to_cb_def, CaseEq "prod", CaseEq "option"]
    >> rename [‘bind 0 args = (vs,n')’]
    >> gvs [evaluate_def, cb_to_bvi_def, evaluate_def]
    >> gvs [CaseEq "prod"]
    >> qmatch_asmsub_rename_tac ‘evaluate (args,env,s) = (res,_)’
    >> Cases_on ‘res’ >> gvs []
    >> drule evaluate_binders
    >> disch_then drule
    >> disch_then $ qspec_then ‘[]’ mp_tac
    >> strip_tac
    >> gvs []
    >> rw []
    >> drule evaluate_vars_expand_env
    >> disch_then $ qspec_then ‘extras’ mp_tac
    >> strip_tac
    >> gvs [])
  >- (* op *)
   (gvs [bvi_to_cb_aux_def, evaluate_def, cb_to_bvi_def, CaseEq "option"]
    >> Cases_on ‘op’ >> gvs [dest_Cons_def]
    >> Cases_on ‘b’ >> gvs [dest_Cons_def]
    >> gvs [CaseEq "prod", CaseEq "sum", PULL_EXISTS]
    >> first_x_assum drule
    >> gvs []
    >> strip_tac
    >> first_assum $ irule_at Any
    >> conj_tac
    >-
     (rw []
      >> gvs [cb_to_bvi_def, evaluate_def])
    >> rw []
    >- gvs [CaseEq "result", CaseEq "error_result"]
    >> gvs [CaseEq "result", CaseEq "error_result"])
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  (* [] *)
  >- gvs [bvi_to_cb_aux_def]
  (* [exp] - dispatch to the single-expression case *)
  >- (gvs [bvi_to_cb_aux_def] >> first_x_assum drule >> gvs [])
  (* Cons *)
  >> rename [‘CallBlock _ left child right’, ‘evaluate ([Op _ (x1::x2::xs)],_,_) = _’]
  >> gvs [bvi_to_cb_aux_def, CaseEq "prod", CaseEq "option", CaseEq "sum", CaseEq "call_block", CaseEq "list"]
  >- (* INL *)
   (first_x_assum $ qspecl_then [‘env’, ‘s’] mp_tac
    >> gvs [evaluate_def, CaseEq "prod"]
    >> CASE_TAC >> gvs []
    >-
     (gvs [CaseEq "call_block", CaseEq "list"]
      >> gvs [do_app_def, do_app_aux_def]
      >> gvs [CaseEq "prod"]
      >> strip_tac
      >> gvs [evaluate_APPEND]
      >> Cases_on ‘as’ >> gvs []
      >> imp_res_tac evaluate_bvi_to_cb_aux_inl
      >> gvs []
      >> gvs [cb_to_bvi_def, evaluate_def]
      >> simp [Once evaluate_CONS, evaluate_def]
      >> first_assum $ qspec_then ‘v’ mp_tac
      >> strip_tac
      >> gvs [CaseEq "prod", CaseEq "result", do_app_def, do_app_aux_def, bvl_to_bvi_id]
      >> gvs [PULL_EXISTS]
      >> gvs [GSYM PULL_FORALL]
      >> first_assum $ qspec_then ‘s'’ mp_tac
      >> strip_tac
      >> imp_res_tac evaluate_IMP_LENGTH
      >> gvs [evaluate_shift_vars]
      >> gen_tac
      >> imp_res_tac evaluate_SING_IMP
      >> gvs []
      >> simp [Once evaluate_CONS]
      >> first_x_assum $ qspec_then ‘v ++ extras’ mp_tac
      >> strip_tac
      >> gvs []
      >> qspecl_then [‘vs2’, ‘v ++ extras’, ‘s'’, ‘a'’] mp_tac evaluate_shift_vars
      >> strip_tac
      >> gvs []
      >> first_x_assum $ qspec_then ‘s'’ mp_tac
      >> strip_tac
      >> drule evaluate_vars_expand_env
      >> disch_then $ qspec_then ‘extras’ mp_tac
      >> strip_tac
      >> gvs [])
    >> strip_tac
    >> gvs [CaseEq "call_block", CaseEq "list"]
    >> gvs [evaluate_APPEND]
    >> Cases_on ‘as’ >> gvs []
    >> imp_res_tac evaluate_bvi_to_cb_aux_inl
    >> gvs []
    >> gvs [cb_to_bvi_def, evaluate_def]
    >> simp [Once evaluate_CONS, evaluate_def]
    >> gvs [CaseEq "prod"]
    >> first_assum $ qspec_then ‘v’ mp_tac
    >> strip_tac
    >> gvs [CaseEq "prod", CaseEq "result", do_app_def, do_app_aux_def, bvl_to_bvi_id]
    >> rw []
    >> simp [Once evaluate_CONS]
    >> first_assum $ qspec_then ‘v ++ extras’ mp_tac
    >> strip_tac
    >> fs [])
  (* INR *)
  >> Cases_on ‘cb’ >> gvs [shift_cb_def]
  >> rename [‘CallBlock tag (0::shift_vars 1 left) (shift_cb 1 child) (shift_vars 1 right)’]
  >> simp [Once evaluate_CONS]
  >> gvs [evaluate_def, CaseEq "prod"]
  >> Cases_on ‘v4’ >> gvs []
  >> gvs [CaseEq "prod"]
  >> gvs [PULL_EXISTS]
  >> first_x_assum drule
  >> CASE_TAC >> gvs []
  >-
   (gvs [do_app_def, do_app_aux_def]
    >> strip_tac
    >> gvs []
    >> CASE_TAC >> gvs []
    >> gvs [cb_to_bvi_def, evaluate_def]
    >> simp [Once evaluate_CONS, evaluate_def]
    >> gvs [evaluate_APPEND]
    >> gvs [evaluate_shift_vars_sing]
    >> CASE_TAC
    >> gvs [CaseEq "prod", CaseEq "result", evaluate_shift_cb_sing]
    >> gvs [do_app_def, do_app_aux_def]
    >> rw []
    >> simp [Once evaluate_CONS, evaluate_def, evaluate_APPEND]
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [bvl_to_bvi_id, evaluate_shift_vars_sing]
    >> first_assum $ qspec_then ‘extras’ mp_tac
    >> strip_tac
    >> gvs [evaluate_shift_cb_sing])
  >> strip_tac
  >> gvs []
  >> reverse CASE_TAC >> gvs []
  >> gvs [cb_to_bvi_def, evaluate_def]
  >> simp [Once evaluate_CONS, evaluate_def]
  >> gvs [evaluate_APPEND, evaluate_def]
  >> gvs [evaluate_shift_vars_sing]
  >> gvs [CaseEq "prod", evaluate_shift_cb_sing]
  >> conj_tac
  >- gvs [CaseEq "prod", CaseEq "result", do_app_def, do_app_aux_def]
  >> rw []
  >> simp [Once evaluate_CONS, evaluate_def, evaluate_APPEND, evaluate_shift_vars_sing]
  >> first_assum $ qspec_then ‘extras’ mp_tac
  >> strip_tac
  >> gvs [CaseEq "prod", CaseEq "result", do_app_def, do_app_aux_def, evaluate_shift_cb_sing]);
val _ = show "evaluate_bvi_to_cb_aux_inr_lemma_replay_typed" inr_local_replay;
val _ = show "evaluate_bvi_to_cb_aux_inr_typed" bvi_tmcProofTheory.evaluate_bvi_to_cb_aux_inr;
val _ = show "hole_has_val_submap_typed" bvi_tmcProofTheory.hole_has_val_submap;
val _ = show "holes_unchanged_except_trans_typed" bvi_tmcProofTheory.holes_unchanged_except_trans;
val _ = show "holes_still_not_finalised_trans_typed" bvi_tmcProofTheory.holes_still_not_finalised_trans;
val _ = show "hole_not_finalised_def_typed" bvi_tmcProofTheory.hole_not_finalised_def;
val _ = show "holes_still_not_finalised_def_typed" bvi_tmcProofTheory.holes_still_not_finalised_def;
val _ = show "holes_still_not_finalised_refl_typed" bvi_tmcProofTheory.holes_still_not_finalised_refl;
val _ = show "holes_still_not_finalised_ins_typed" bvi_tmcProofTheory.holes_still_not_finalised_ins;
val _ = show "holes_still_not_finalised_del_typed" bvi_tmcProofTheory.holes_still_not_finalised_del;
val _ = show "only_fresh_def_typed" bvi_tmcProofTheory.only_fresh_def;
val _ = show "state_rel_with_clock_typed" bvi_tmcProofTheory.state_rel_with_clock;
val _ = show "state_rel_dec_typed" bvi_tmcProofTheory.state_rel_dec;
val _ = show "v_rel_submap_typed" bvi_tmcProofTheory.v_rel_submap;
val _ = show "list_rel_submap_typed" bvi_tmcProofTheory.list_rel_submap;
val _ = show "env_rel_submap_typed" bvi_tmcProofTheory.env_rel_submap;
val _ = show "ref_rel_submap_typed" bvi_tmcProofTheory.ref_rel_submap;
val _ = show "env_rel_relax_opt_typed" bvi_tmcProofTheory.env_rel_relax_opt;
val _ = show "env_rel_cons_typed" bvi_tmcProofTheory.env_rel_cons;
val _ = show "env_rel_append_typed" bvi_tmcProofTheory.env_rel_append;
val _ = show "env_rel_el_v_rel_typed" bvi_tmcProofTheory.env_rel_el_v_rel;
val _ = show "env_rel_el_typed" bvi_tmcProofTheory.env_rel_el;
val _ = show "list_rel_env_rel_typed" bvi_tmcProofTheory.list_rel_env_rel;
val _ = show "env_rel_length_opt_typed" bvi_tmcProofTheory.env_rel_length_opt;
val _ = show "env_rel_length_non_opt_typed" bvi_tmcProofTheory.env_rel_length_non_opt;
val _ = show "env_rel_length_typed" bvi_tmcProofTheory.env_rel_length;
val _ = show "env_rel_extras_opt_typed" bvi_tmcProofTheory.env_rel_extras_opt;
val _ = show "env_rel_strip_extras_typed" bvi_tmcProofTheory.env_rel_strip_extras;
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
val number_list_rel = Q.prove
  (`∀g ns ys f. LIST_REL (v_rel f) (MAP (Number o g) ns) ys ⇒ ys = MAP (Number o g) ns`,
   Induct_on `ns` >> rw [] >> gvs [] >> qpat_x_assum `v_rel _ _ _` mp_tac
   >> simp [Once v_rel_cases] >> rw [] >> res_tac >> gvs []);
val _ = show "list_rel_v_rel_number_replay_typed" number_list_rel;
val word_list_rel = Q.prove
  (`∀ns ys f. LIST_REL (v_rel f) (MAP Word64 ns) ys ⇒ ys = MAP Word64 ns`,
   Induct_on `ns` >> rw [] >> gvs [] >> qpat_x_assum `v_rel _ _ _` mp_tac
   >> simp [Once v_rel_cases] >> rw [] >> res_tac >> gvs []);
val _ = show "list_rel_v_rel_word_replay_typed" word_list_rel;
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

(* Replay the original mutual extraction-label theorem. *)
val extraction_labels = Q.prove
  (`(∀n loc tag exp bs r.
       bvi_tmc$bvi_to_cb_aux_sing n loc tag exp = SOME (bs,r) ⇒
       BIGUNION (set (MAP bviProps$get_code_labels bs)) ⊆ bviProps$get_code_labels exp) ∧
     (∀n loc tag args bs r.
       bvi_tmc$bvi_to_cb_aux n loc tag args = SOME (bs,r) ⇒
       BIGUNION (set (MAP bviProps$get_code_labels bs)) ⊆
       BIGUNION (set (MAP bviProps$get_code_labels args)))`,
   ho_match_mp_tac bvi_tmcTheory.bvi_to_cb_aux_ind
   \\ rw []
   \\ gvs [bvi_tmcTheory.bvi_to_cb_aux_def, bvi_tmcTheory.call_to_cb_def,
           CaseEq "call_block", CaseEq "prod", CaseEq "option", CaseEq "sum", CaseEq "list"]
   \\ gvs [SUBSET_DEF] \\ rw [] \\ res_tac \\ gvs []);
val _ = show "bvi_to_cb_aux_code_labels_lemma_replay_typed" extraction_labels;

val to_block_labels = Q.prove
  (`∀n loc exp bs cb.
      bvi_tmc$bvi_to_cb n loc exp = SOME (bs,cb) ⇒
      BIGUNION (set (MAP bviProps$get_code_labels bs)) ⊆ bviProps$get_code_labels exp`,
   Cases_on `exp`
   \\ gvs [bvi_tmcTheory.bvi_to_cb_def, bvi_tmcTheory.call_to_cb_def, CaseEq "prod", CaseEq "option", CaseEq "sum"]
   \\ rw []
   >- gvs [SUBSET_DEF]
   \\ drule (cj 2 extraction_labels)
   \\ gvs [SUBSET_DEF]);
val _ = show "bvi_to_cb_code_labels_replay_typed" to_block_labels;

val rewrite_wrapper_labels = Q.prove
  (`∀loc loc_opt n exp y.
      bvi_tmc$rewrite_wrapper loc loc_opt n exp = SOME y ⇒
      bviProps$get_code_labels y ⊆ bviProps$get_code_labels exp ∪ {loc_opt}`,
   recInduct bvi_tmcTheory.rewrite_wrapper_ind
   \\ rw [bvi_tmcTheory.rewrite_wrapper_def]
   \\ gvs [CaseEq "option", CaseEq "prod", CaseEq "call_block", wrapper_labels]
   \\ imp_res_tac to_block_labels
   \\ gvs [SUBSET_DEF] \\ rw [] \\ res_tac \\ gvs []);
val _ = show "rewrite_wrapper_code_labels_replay_typed" rewrite_wrapper_labels;

val rewrite_worker_labels = Q.prove
  (`∀loc loc_opt p i n exp.
      bviProps$get_code_labels (bvi_tmc$rewrite_worker loc loc_opt p i n exp) ⊆
      bviProps$get_code_labels exp ∪ {loc_opt}`,
   recInduct bvi_tmcTheory.rewrite_worker_ind
   \\ rw [bvi_tmcTheory.rewrite_worker_def, bvi_tmcTheory.fill_hole_def,
          closLangTheory.assign_get_code_label_def]
   \\ every_case_tac
   \\ gvs [bvi_tmcTheory.fill_hole_def, closLangTheory.assign_get_code_label_def, worker_labels]
   \\ imp_res_tac to_block_labels
   \\ gvs [SUBSET_DEF] \\ rw [] \\ res_tac \\ gvs []);
val _ = show "rewrite_worker_code_labels_replay_typed" rewrite_worker_labels;

val compile_exp_labels = Q.prove
  (`bvi_tmc$compile_exp loc next arity exp = SOME (exp_w,exp_k) ⇒
      bviProps$get_code_labels exp_w ⊆ bviProps$get_code_labels exp ∪ {next} ∧
      bviProps$get_code_labels exp_k ⊆ bviProps$get_code_labels exp ∪ {next}`,
   rw [bvi_tmcTheory.compile_exp_def, CaseEq "option"]
   \\ imp_res_tac rewrite_wrapper_labels
   \\ gvs [rewrite_worker_labels]);
val _ = show "compile_exp_code_labels_replay_typed" compile_exp_labels;

val _ = show "compile_each_good_code_labels_typed" bvi_tmcProofTheory.compile_each_good_code_labels;
val _ = show "compile_prog_good_code_labels_typed" bvi_tmcProofTheory.compile_prog_good_code_labels;
val _ = show "compile_prog_semantics_typed" bvi_tmcProofTheory.compile_prog_semantics;
val _ = show "compile_each_semantics_typed" bvi_tmcProofTheory.compile_each_semantics;
