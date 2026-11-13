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
