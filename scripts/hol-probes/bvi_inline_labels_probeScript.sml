(* Typed original source equations and label-preservation theorem. *)
load "bvi_inlineTheory";
load "bvi_inlineProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "remove_ticks_exp_def_typed" bvi_inlineTheory.remove_ticks_exp_def;
val _ = show "remove_ticks_get_code_labels_typed" bvi_inlineProofTheory.remove_ticks_get_code_labels;
val _ = show "remove_ticks_prog_code_labels_typed" bvi_inlineProofTheory.remove_ticks_prog_code_labels;
val _ = show "MAP_FST_remove_ticks_prog_typed" bvi_inlineProofTheory.MAP_FST_remove_ticks_prog;
val _ = show "inline_all_def_typed" bvi_inlineTheory.inline_all_def;
val _ = show "compile_inc_def_typed" bvi_inlineTheory.compile_inc_def;
val _ = show "compile_inc_code_labels_typed" bvi_inlineProofTheory.compile_inc_code_labels;
val _ = show "inline_all_MAP_FST_typed" bvi_inlineProofTheory.inline_all_MAP_FST;
val _ = show "compile_inc_MAP_FST_typed" bvi_inlineProofTheory.compile_inc_MAP_FST;
val _ = show "inline_exp_def_typed" bvi_inlineTheory.inline_exp_def;
val _ = show "cache_code_labels_def_typed" bvi_inlineProofTheory.cache_code_labels_def;
val _ = show "lookup_cache_code_labels_typed" bvi_inlineProofTheory.lookup_cache_code_labels;
val _ = show "cache_code_labels_insert_typed" bvi_inlineProofTheory.cache_code_labels_insert;
val _ = show "bvi_mk_tick_get_code_labels_typed" bvi_inlineProofTheory.bvi_mk_tick_get_code_labels;
val _ = show "inline_exp_code_labels_typed" bvi_inlineProofTheory.inline_exp_code_labels;
val _ = show "compile_prog_def_typed" bvi_inlineTheory.compile_prog_def;
val _ = show "inline_all_code_labels_typed" bvi_inlineProofTheory.inline_all_code_labels;
val _ = show "compile_prog_code_labels_typed" bvi_inlineProofTheory.compile_prog_code_labels;
val _ = show "compile_prog_semantics_typed" bvi_inlineProofTheory.compile_prog_semantics;

(* Replay the original local semantics safety proofs. *)
load "preamble";
open preamble bviSemTheory;
val semantics_not_Fail_cond_replay = Q.prove
  (`∀ffi code co cc start.
    semantics ffi code co cc start ≠ Fail ⇒
    ¬∃j e. FST (evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc j)) = Rerr e ∧
      e ≠ Rabort Rtimeout_error ∧ ∀f. e ≠ Rabort (Rffi_error f)`,
   rpt strip_tac
  >> qpat_x_assum `semantics _ _ _ _ _ ≠ Fail` mp_tac
  >> simp [semantics_def]
  >> IF_CASES_TAC
  >- simp []
  >> fs []
  >> qpat_x_assum `∀a b. _` (qspecl_then [`j`,`e`] mp_tac)
  >> fs []);
val _ = show "semantics_not_Fail_cond_replay_typed" semantics_not_Fail_cond_replay;
val semantics_no_type_error_replay = Q.prove
  (`∀ffi code co cc start.
    semantics ffi code co cc start ≠ Fail ⇒
    ∀j. FST (evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc j)) ≠ Rerr (Rabort Rtype_error)`,
   rpt strip_tac
  >> drule semantics_not_Fail_cond_replay
  >> simp []
  >> qexistsl [`j`,`Rabort Rtype_error`]
  >> gvs []);
val _ = show "semantics_no_type_error_replay_typed" semantics_no_type_error_replay;

(* Replay the remaining original local semantics observations. *)
load "bviPropsTheory";
open bviPropsTheory;
val semantics_terminate_unique_replay = Q.prove
  (`∀ffi code co cc start k1 r1 t1 k2 r2 t2.
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc k1) = (r1,t1) ∧
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc k2) = (r2,t2) ∧
    r1 ≠ Rerr (Rabort Rtimeout_error) ∧
    r2 ≠ Rerr (Rabort Rtimeout_error) ⇒
    r1 = r2 ∧ t1.ffi = t2.ffi`,
   rpt gen_tac
  >> strip_tac
  >> qpat_assum `evaluate (_,_,initial_state _ _ _ _ k1) = _` assume_tac
  >> drule evaluate_add_clock
  >> fs [inc_clock_def]
  >> disch_then (qspec_then `k2` assume_tac)
  >> qpat_assum `evaluate (_,_,initial_state _ _ _ _ k2) = _` assume_tac
  >> drule evaluate_add_clock
  >> fs [inc_clock_def]
  >> disch_then (qspec_then `k1` assume_tac)
  >> fs [state_component_equality]);
val _ = show "semantics_terminate_unique_replay_typed" semantics_terminate_unique_replay;
val semantics_error_cases_replay = Q.prove
  (`∀ffi code co cc start.
    semantics ffi code co cc start ≠ Fail ⇒
    ∀j e t. evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi code co cc j) = (Rerr e,t) ⇒
      e = Rabort Rtimeout_error ∨ ∃f. e = Rabort (Rffi_error f)`,
   rpt strip_tac
  >> drule semantics_not_Fail_cond_replay
  >> rw []
  >> first_x_assum (qspecl_then [`j`,`e`] mp_tac)
  >> gvs []);
val _ = show "semantics_error_cases_replay_typed" semantics_error_cases_replay;

(* The local theorem is not exported; capture its original statement with
   inferred types. This is a typed term, not a replay of its proof. *)
load "backendPropsTheory";
open bvi_inlineTheory backendPropsTheory;
val evaluate_compile_prog_statement =
  ``∀prog cs1 prog1 co ffi cc k start r s.
  compile_prog prog = (cs1,prog1) ∧
  FST (FST (co 0)) = cs1 ∧
  ALL_DISTINCT (MAP FST prog) ∧
  (∀j. FST (evaluate ([Call 0 (SOME start) [] NONE],[],
         initial_state ffi (fromAList prog) co
           (state_cc compile_inc cc) j)) ≠ Rerr (Rabort Rtype_error)) ∧
  evaluate ([Call 0 (SOME start) [] NONE],[],
    initial_state ffi (fromAList prog1) (state_co compile_inc co) cc k) =
      (r,s) ⇒
  ∃ck s2.
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi (fromAList prog) co
        (state_cc compile_inc cc) (k + ck)) = (r,s2) ∧
    s2.ffi = s.ffi``;
val _ = (print "evaluate_compile_prog_statement_typed=";
         print_term evaluate_compile_prog_statement; print "\n");

(* The local theorem is not exported; capture the source statement and
   its inferred types without claiming a proof replay. *)
open bvi_inlineProofTheory;
val evaluate_remove_ticks_compile_statement =
  ``∀prog co ffi cc k start r s.
  evaluate ([Call 0 (SOME start) [] NONE],[],
    initial_state ffi (fromAList (clean_prog prog))
      (remove_ticks_co ∘ co) cc k) = (r,s) ⇒
  ∃ck s2.
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi (fromAList prog) co (remove_ticks_cc cc) (k + ck)) =
        (r,s2) ∧
    s2.ffi = s.ffi``;
val _ = (print "evaluate_remove_ticks_compile_statement_typed=";
         print_term evaluate_remove_ticks_compile_statement; print "\n");

val _ = show "clean_prog_def_typed" bvi_inlineProofTheory.clean_prog_def;
val _ = show "remove_ticks_cc_def_typed" bvi_inlineProofTheory.remove_ticks_cc_def;
val _ = show "remove_ticks_co_def_typed" bvi_inlineProofTheory.remove_ticks_co_def;

(* The local inlining lemma's original statement, with inferred types. *)
val evaluate_inline_compile_statement =
  ``∀prog cs1 prog1 co ffi cc k start r s.
  inline_all LN prog = (cs1,prog1) ∧
  FST (FST (co 0)) = cs1 ∧
  ALL_DISTINCT (MAP FST prog) ∧
  evaluate ([Call 0 (SOME start) [] NONE],[],
    initial_state ffi (fromAList prog) co (state_cc inline_all cc) k) =
      (r,s) ∧
  r ≠ Rerr (Rabort Rtype_error) ⇒
  ∃s2.
    evaluate ([Call 0 (SOME start) [] NONE],[],
      initial_state ffi (fromAList prog1) (state_co inline_all co) cc k) =
        (r,s2) ∧
    in_state_rel s s2``;
val _ = (print "evaluate_inline_compile_statement_typed=";
         print_term evaluate_inline_compile_statement; print "\n");

(* The local initial-state relation lemma's original typed statement. *)
val inline_initial_state_rel_statement =
  ``∀prog cs1 prog1 co ffi cc clk.
  inline_all LN prog = (cs1,prog1) ∧
  FST (FST (co 0)) = cs1 ∧
  ALL_DISTINCT (MAP FST prog) ⇒
  in_state_rel
    (initial_state ffi (fromAList prog) co (state_cc inline_all cc) clk)
    (initial_state ffi (fromAList prog1) (state_co inline_all co) cc clk)``;
val _ = (print "inline_initial_state_rel_statement_typed=";
         print_term inline_initial_state_rel_statement; print "\n");

(* Replay the original local clock/I/O-event monotonicity proof. *)
val evaluate_add_clock_io_events_mono_replay = Q.prove
  (`∀exps env (s:('c,'ffi) bviSem$state) k extra.
    (SND (evaluate (exps,env,s with clock := k))).ffi.io_events ≼
    (SND (evaluate (exps,env,s with clock := k + extra))).ffi.io_events`,
   rpt strip_tac
  >> qspecl_then [`exps`,`env`,`s with clock := k`,`extra`] mp_tac
       evaluate_add_to_clock_io_events_mono
  >> simp [inc_clock_def]);
val _ = show "evaluate_add_clock_io_events_mono_replay_typed"
  evaluate_add_clock_io_events_mono_replay;

(* Original adapter definitions and their local equalities. *)
val _ = show "in_cc_def_typed" bvi_inlineProofTheory.in_cc_def;
val _ = show "in_co_def_typed" bvi_inlineProofTheory.in_co_def;
val in_cc_eq_state_cc_replay = Q.prove
  (`in_cc cc = state_cc inline_all cc`,
   rw [in_cc_def, state_cc_def, FUN_EQ_THM, FORALL_PROD]
  >> rpt (pairarg_tac >> fs []));
val _ = show "in_cc_eq_state_cc_replay_typed" in_cc_eq_state_cc_replay;
val in_co_eq_state_co_replay = Q.prove
  (`in_co co = state_co inline_all co`,
   rw [in_co_def, state_co_def, FUN_EQ_THM]
  >> rpt (pairarg_tac >> fs []));
val _ = show "in_co_eq_state_co_replay_typed" in_co_eq_state_co_replay;

(* The original incremental compiler/oracle factorization and proofs. *)
val _ = show "state_cc_compile_inc_eq_typed" bvi_inlineProofTheory.state_cc_compile_inc_eq;
val _ = show "state_co_compile_inc_eq_typed" bvi_inlineProofTheory.state_co_compile_inc_eq;
val state_cc_compile_inc_eq_replay = Q.prove
  (`state_cc compile_inc cc = state_cc inline_all (remove_ticks_cc cc)`,
   rw [state_cc_def, compile_inc_def, remove_ticks_cc_def, FUN_EQ_THM]
  >> rpt (pairarg_tac >> gvs [clean_prog_def]));
val _ = show "state_cc_compile_inc_eq_replay_typed" state_cc_compile_inc_eq_replay;
val state_co_compile_inc_eq_replay = Q.prove
  (`state_co compile_inc co = remove_ticks_co ∘ state_co inline_all co`,
   rw [state_co_def, compile_inc_def, remove_ticks_co_def, FUN_EQ_THM]
  >> rpt (pairarg_tac >> gvs [clean_prog_def]));
val _ = show "state_co_compile_inc_eq_replay_typed" state_co_compile_inc_eq_replay;

(* The full tick-removal evaluation theorem, including its inferred types. *)
val _ = show "evaluate_remove_ticks_typed" bvi_inlineProofTheory.evaluate_remove_ticks;

(* The local mutual theorem is not exported; capture its original typed statement. *)
val evaluate_remove_ticks_mutual_statement =
  ``∀k.
    (∀e env (t:('c,'ffi) bviSem$state) s res t1.
       remove_state_rel s t ∧ t.clock ≤ k ∧
       evaluate ([remove_ticks_exp e],env,t) = (res,t1) ⇒
       ∃extra s1.
         evaluate ([e],env,s with clock := s.clock + extra) =
           (res,s1) ∧ remove_state_rel s1 t1) ∧
    (∀es env (t:('c,'ffi) bviSem$state) s res t1.
       remove_state_rel s t ∧ t.clock ≤ k ∧
       evaluate (remove_ticks_exps es,env,t) = (res,t1) ⇒
       ∃extra s1.
         evaluate (es,env,s with clock := s.clock + extra) =
           (res,s1) ∧ remove_state_rel s1 t1)``;
val _ = (print "evaluate_remove_ticks_mutual_statement_typed=";
         print_term evaluate_remove_ticks_mutual_statement; print "\n");

(* Original local primitive-operation relation statement, with inferred types. *)
val remove_state_rel_do_app_statement =
  ``∀op args (s:('c,'ffi) bviSem$state) t.
    remove_state_rel s t ⇒
      case do_app op args s of
      | Rval (value,s1) =>
          ∃t1. do_app op args t = Rval (value,t1) ∧ remove_state_rel s1 t1
      | Rerr err => do_app op args t = Rerr err``;
val _ = (print "remove_state_rel_do_app_statement_typed=";
         print_term remove_state_rel_do_app_statement; print "\n");

(* Original local installation relation, including independent result types. *)
val remove_state_rel_do_install_statement =
  ``∀args (s:('c,'ffi) bviSem$state) t.
    remove_state_rel s t ⇒
      case do_install args s of
      | Rval (value,s1) =>
          ∃t1. do_install args t = Rval (value,t1) ∧ remove_state_rel s1 t1
      | Rerr err => do_install args t = Rerr err``;
val _ = (print "remove_state_rel_do_install_statement_typed=";
         print_term remove_state_rel_do_install_statement; print "\n");

(* Replay the original local clean-program simplification lemmas. *)
val clean_prog_CONS_replay = Q.prove
  (`clean_prog [] = [] ∧
    clean_prog (p::ps) = (I ## I ## remove_ticks_exp) p :: clean_prog ps`,
   simp [clean_prog_def, PAIR_MAP, ELIM_UNCURRY]);
val _ = show "clean_prog_CONS_replay_typed" clean_prog_CONS_replay;
val clean_prog_simps_replay = Q.prove
  (`MAP FST (clean_prog prog) = MAP FST prog ∧
    map (I ## remove_ticks_exp) (fromAList prog) = fromAList (clean_prog prog)`,
   conj_tac
  >> Induct_on `prog`
  >> simp [clean_prog_def, fromAList_def, map_insert, FORALL_PROD]);
val _ = show "clean_prog_simps_replay_typed" clean_prog_simps_replay;

(* Replay the original local clock arithmetic and evaluator lemmas. *)
val clock_sub_lt_replay = Q.prove
  (`∀x k:num. x ≠ 0 ∧ x ≤ k ⇒ x - 1 < k`,
   rpt strip_tac
  >> fs [NOT_ZERO]
  >> irule SUB_LESS
  >> fs []);
val _ = show "clock_sub_lt_replay_typed" clock_sub_lt_replay;
val evaluate_add_extra_clock_replay = Q.prove
  (`∀xs env (s:('c,'ffi) bviSem$state) res s1 extra extra'.
    evaluate (xs,env,s with clock := extra + s.clock) = (res,s1) ∧
    res ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate (xs,env,s with clock := extra + extra' + s.clock) =
      (res,s1 with clock := extra' + s1.clock)`,
   rpt strip_tac
  >> drule_all evaluate_add_clock
  >> disch_then (qspec_then `extra'` mp_tac)
  >> simp [inc_clock_def]);
val _ = show "evaluate_add_extra_clock_replay_typed" evaluate_add_extra_clock_replay;

(* Replay the local tick-removal code-lookup lemma. *)
val remove_state_rel_find_code_eq_replay = Q.prove
  (`∀s (t:('c,'ffi) bviSem$state).
    remove_state_rel s t ⇒
    ∀dest vs.
      find_code dest vs t.code =
        OPTION_MAP (I ## remove_ticks_exp) (find_code dest vs s.code)`,
   rpt strip_tac
  >> gvs [remove_state_rel_def]
  >> Cases_on `dest`
  >> gvs [bvlSemTheory.find_code_def, lookup_map]
  >> every_case_tac
  >> gvs []);
val _ = show "remove_state_rel_find_code_eq_replay_typed" remove_state_rel_find_code_eq_replay;
val _ = show "remove_state_rel_def_typed" bvi_inlineProofTheory.remove_state_rel_def;

(* Original exported empty-list and complete inliner simulation theorems. *)
val _ = show "remove_ticks_exps_NIL_typed" bvi_inlineProofTheory.remove_ticks_exps_NIL;
val _ = show "evaluate_inline_typed" bvi_inlineProofTheory.evaluate_inline;
