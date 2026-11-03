(* Typed source precondition for closure known-function optimization. *)
load "clos_knownProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "syntax_ok_typed=" clos_knownProofTheory.syntax_ok_def;
val _ = show "bag_all_distinct_typed=" bagTheory.BAG_ALL_DISTINCT;
val _ = show "option_val_approx_spt_typed=" clos_knownTheory.option_val_approx_spt_def;
val _ = show "option_upd_val_spt_typed=" clos_knownTheory.option_upd_val_spt_def;
val _ = show "contains_closures_typed=" clos_knownTheory.contains_closures_def;
val _ = show "merge_typed=" clos_knownTheory.merge_def;
val _ = show "known_op_typed=" clos_knownTheory.known_op_def;
val _ = show "get_size_aux_typed=" clos_knownTheory.get_size_aux_def;
val _ = show "get_size_typed=" clos_knownTheory.get_size_def;
val _ = show "get_size_sc_aux_typed=" clos_knownTheory.get_size_sc_aux_def;
val _ = show "get_size_sc_typed=" clos_knownTheory.get_size_sc_def;
val _ = show "clos_approx_typed=" clos_knownTheory.clos_approx_def;
val _ = show "clos_gen_noinline_typed=" clos_knownTheory.clos_gen_noinline_def;
val _ = show "mk_ticks_typed=" clos_knownTheory.mk_Ticks_def;
val _ = show "get_size_sc_aux_correct_typed=" clos_knownTheory.get_size_sc_aux_correct;
val _ = show "get_size_sc_some_typed=" clos_knownTheory.get_size_sc_SOME;
val _ = show "free_typed=" clos_knownTheory.free_def;
val _ = show "closed_typed=" clos_knownTheory.closed_def;
val _ = show "decide_inline_typed=" clos_knownTheory.decide_inline_def;
val _ = show "decide_inline_positive_typed=" clos_knownTheory.decide_inline_LetInline;
val _ = show "fv_max_def_typed=" clos_knownProofTheory.fv_max_def;
val _ = show "fv_max_smart_typed=" clos_knownProofTheory.fv_max_SmartOp;
val _ = show "fv_max_cons_typed=" clos_knownProofTheory.fv_max_cons;
val _ = show "fv_max_append_typed=" clos_knownProofTheory.fv_max_append;
val _ = show "fv_max_less_typed=" clos_knownProofTheory.fv_max_less;
val _ = show "fv_max_rw_typed=" clos_knownProofTheory.fv_max_rw;
val _ = show "fv_max_ticks_typed=" clos_knownProofTheory.fv_max_mk_Ticks;
val _ = show "val_approx_val_rules_typed=" clos_knownProofTheory.val_approx_val_rules;
val _ = show "val_approx_merge_left_typed=" clos_knownProofTheory.val_approx_val_merge_I_lemma;
val _ = show "val_approx_merge_typed=" clos_knownProofTheory.val_approx_val_merge_I;
val _ = show "known_merge_comm_typed=" clos_knownPropsTheory.merge_comm;
val _ = show "state_globals_approx_typed=" clos_knownProofTheory.state_globals_approx_def;
val _ = show "state_globals_clock_typed=" clos_knownProofTheory.state_globals_approx_clock_fupd;
val _ = show "state_globals_dec_clock_typed=" clos_knownProofTheory.state_globals_approx_dec_clock;
val _ = show "state_globals_refs_typed=" clos_knownProofTheory.state_globals_approx_refsfupd;
val _ = show "state_globals_ffi_typed=" clos_knownProofTheory.state_globals_approx_ffifupd;
val _ = show "state_globals_code_typed=" clos_knownProofTheory.state_globals_approx_codeupd;
val _ = show "state_globals_oracle_typed=" clos_knownProofTheory.state_globals_approx_coupd;
val _ = show "known_op_correct_approx_typed=" clos_knownProofTheory.known_op_correct_approx;
val _ = show "val_approx_sgc_free_typed=" clos_knownProofTheory.val_approx_sgc_free_def;
val _ = show "val_approx_sgc_free_merge_typed=" clos_knownProofTheory.val_approx_sgc_free_merge;
val _ = show "globals_approx_sgc_free_typed=" clos_knownProofTheory.globals_approx_sgc_free_def;
val _ = show "known_op_preserves_esgc_free_typed=" clos_knownProofTheory.known_op_preserves_esgc_free;
val _ = show "elist_globals_empty_typed=" clos_knownProofTheory.elist_globals_empty;
val _ = show "clos_gen_noinline_safe_typed=" clos_knownProofTheory.clos_gen_noinline_val_approx_sgc_free;
val _ = show "decide_inline_imp_clos_typed=" clos_knownProofTheory.decide_inline_LetInline_IMP_Clos;
val _ = show "decide_inline_imp_clos_lopt_typed=" clos_knownProofTheory.decide_inline_LetInline_IMP_Clos_lopt;
val _ = show "known_def_typed=" clos_knownTheory.known_def;
val _ = show "known_length_typed=" clos_knownTheory.known_LENGTH;
val _ = show "known_length_eq_typed=" clos_knownTheory.known_LENGTH_EQ_E;
val _ = show "known_sing_typed=" clos_knownTheory.known_sing;
val _ = show "known_sing_eq_typed=" clos_knownTheory.known_sing_EQ_E;
val _ = show "mapped_globals_typed=" clos_knownProofTheory.mapped_globals_def;
val _ = show "mglobals_extend_typed=" clos_knownProofTheory.mglobals_extend_def;
val _ = show "mglobals_extend_refl_typed=" clos_knownProofTheory.mglobals_extend_refl;
val _ = show "mglobals_extend_trans_typed=" clos_knownProofTheory.mglobals_extend_trans;
val _ = show "mglobals_extend_subset_typed=" clos_knownProofTheory.mglobals_extend_SUBSET;
val _ = show "state_globals_approx_subspt_typed=" clos_knownProofTheory.state_globals_approx_subspt;
val _ = show "known_op_changed_globals_typed=" clos_knownProofTheory.known_op_changed_globals;
val _ = show "known_op_changed_globals_cases_typed=" clos_knownProofTheory.known_op_changed_globals_cases;
val _ = show "known_op_changed_globals_alt_set_typed=" clos_knownProofTheory.known_op_changed_globals_alt_set;
val _ = show "do_app_ssgc_typed=" clos_knownProofTheory.do_app_ssgc;
val _ = show "evaluate_ind_typed=" closSemTheory.evaluate_ind;

(* Local theorem: replay the original statement with explicit theory qualifiers. *)
val _ = (print "evaluate_changed_globals_0_statement_typed="; print_term
 ``(!es env (s0:('c,'ffi) closSem$state) res s.
      closSem$evaluate (es, env, s0) = (res, s) /\
      closProps$ssgc_free s0 /\ EVERY closProps$esgc_free es /\
      EVERY closProps$vsgc_free env ==>
        closProps$ssgc_free s /\ closProps$rsgc_free res /\
        ?n. s.compile_oracle = shift_seq n s0.compile_oracle /\
          clos_knownProof$mglobals_extend s0.globals
            (SET_OF_BAG (closProps$elist_globals es) UNION
             SET_OF_BAG (closProps$elist_globals (FLAT (clos_knownProof$first_n_exps s0.compile_oracle n)))) s.globals) /\
   (!loc_opt f args (s0:('c,'ffi) closSem$state) res s.
      closSem$evaluate_app loc_opt f args s0 = (res, s) /\
      closProps$ssgc_free s0 /\ closProps$vsgc_free f /\ EVERY closProps$vsgc_free args ==>
        closProps$ssgc_free s /\ closProps$rsgc_free res /\
        ?n. s.compile_oracle = shift_seq n s0.compile_oracle /\
          clos_knownProof$mglobals_extend s0.globals
            (SET_OF_BAG (closProps$elist_globals (FLAT (clos_knownProof$first_n_exps s0.compile_oracle n)))) s.globals)``; print "\n");

val _ = show "dest_closure_full_sgc_free_typed=" clos_knownProofTheory.dest_closure_Full_sgc_free;
(* The theorem is local in the source; print its source statement with inferred types. *)
val _ = (print "update_thunk_ssgc_free_statement_typed="; print_term
  ``closProps$ssgc_free s ∧
    EVERY closProps$vsgc_free vs ∧
    closSem$update_thunk [closSem$RefPtr v ptr] s.refs vs = SOME refs ⇒
    closProps$ssgc_free (s with refs := refs)``; print "\n");
val _ = show "first_n_exps_typed=" clos_knownProofTheory.first_n_exps_def;
val _ = show "first_n_exps_shift_seq_typed=" clos_knownProofTheory.first_n_exps_shift_seq;
val _ = show "mem_first_n_exps_typed=" clos_knownProofTheory.MEM_first_n_exps;
val _ = show "shift_seq_zero_typed=" clos_knownProofTheory.shift_seq_zero;
val _ = show "shift_seq_add_typed=" clos_knownProofTheory.shift_seq_add;
val _ = show "ssgc_free_co_shift_seq_typed=" clos_knownProofTheory.ssgc_free_co_shift_seq;
val _ = show "ssgc_free_do_install_typed=" clos_knownProofTheory.ssgc_free_do_install;
val _ = show "do_install_ssgc_typed=" clos_knownProofTheory.do_install_ssgc;
val _ = show "set_globals_empty_esgc_free_typed=" closPropsTheory.set_globals_empty_esgc_free;
val _ = show "vsgc_free_typed=" closPropsTheory.vsgc_free_def;
val _ = show "rsgc_free_typed=" closPropsTheory.rsgc_free_def;
val _ = show "ssgc_free_typed=" closPropsTheory.ssgc_free_def;
val _ = show "vsgc_free_unit_typed=" closPropsTheory.vsgc_free_Unit;
val _ = show "vsgc_free_bool_typed=" closPropsTheory.vsgc_free_Boolv;
val _ = show "ssgc_free_clock_typed=" closPropsTheory.ssgc_free_clockupd;
val _ = show "ssgc_free_dec_clock_typed=" closPropsTheory.ssgc_free_dec_clock;
