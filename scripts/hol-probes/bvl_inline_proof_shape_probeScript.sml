(* Typed statements for the BVL inlining proof's code-label and name-preservation results. *)
load "bvl_inlineProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "var_list_code_labels_imp_typed" bvl_inlineProofTheory.var_list_code_labels_imp;
val _ = show "let_op_code_labels_typed" bvl_inlineProofTheory.let_op_code_labels;
val _ = show "let_op_sing_code_labels_typed" bvl_inlineProofTheory.let_op_sing_code_labels;
val _ = show "remove_ticks_code_labels_typed" bvl_inlineProofTheory.remove_ticks_code_labels;
val _ = show "optimise_get_code_labels_typed" bvl_inlineProofTheory.optimise_get_code_labels;
val _ = show "tick_inline_code_labels_typed" bvl_inlineProofTheory.tick_inline_code_labels;
val _ = show "tick_inline_all_code_labels_typed" bvl_inlineProofTheory.tick_inline_all_code_labels;
val _ = show "compile_prog_get_code_labels_typed" bvl_inlineProofTheory.compile_prog_get_code_labels;
val _ = show "MAP_FST_MAP_optimise_typed" bvl_inlineProofTheory.MAP_FST_MAP_optimise;
val _ = show "compile_prog_names_typed" bvl_inlineProofTheory.compile_prog_names;
val _ = show "handle_ok_optimise_typed" bvl_inlineProofTheory.handle_ok_optimise;
val _ = show "compile_prog_handle_ok_typed" bvl_inlineProofTheory.compile_prog_handle_ok;
val _ = show "map_fromAList_typed" bvl_inlineProofTheory.map_fromAList;
val _ = show "state_cc_compile_inc_eq_typed" bvl_inlineProofTheory.state_cc_compile_inc_eq;
val _ = show "state_co_compile_inc_eq_typed" bvl_inlineProofTheory.state_co_compile_inc_eq;
val _ = show "semantics_remove_ticks_typed" bvl_inlineProofTheory.semantics_remove_ticks;
val _ = show "compile_prog_semantics_typed" bvl_inlineProofTheory.compile_prog_semantics;
val _ = show "let_op_cc_def_typed" bvl_inlineProofTheory.let_op_cc_def;
val _ = show "let_opt_def_typed" bvl_inlineProofTheory.let_opt_def;
val _ = show "let_opt_remove_def_typed" bvl_inlineProofTheory.let_opt_remove_def;
val _ = show "let_state_rel_def_typed" bvl_inlineProofTheory.let_state_rel_def;
val _ = show "evaluate_let_op_typed" bvl_inlineProofTheory.evaluate_let_op;

load "preamble";
open preamble bvl_inlineProofTheory bvl_inlineTheory bvlSemTheory bvlPropsTheory;
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj", "fromAList_def"];
val let_state_rel_alt = let_state_rel_def;
val let_state_rel_def = let_state_rel_def |> SIMP_RULE (srw_ss()) [state_component_equality, GSYM CONJ_ASSOC];
val let_evaluate_Call_replay = prove(
  ``evaluate ([Call 0 (SOME start) []], [],
             initial_state ffi0 prog co (let_op_cc q4 l4 cc) k) = (r, s) /\
    r <> Rerr (Rabort Rtype_error) ⇒
    ∃(s2:('c,'ffi) bvlSem$state).
      evaluate ([Call 0 (SOME start) []], [],
        initial_state ffi0 (map (let_opt q4 l4) prog)
          ((I ## MAP (I ## let_opt q4 l4)) o co) cc k) = (r, s2) ∧
      s2.ffi = s.ffi /\ s.clock = s2.clock``,
  strip_tac \\ fs [let_op_cc_def]
  \\ imp_res_tac evaluate_let_op
  \\ fs [let_op_def]
  \\ qmatch_goalsub_abbrev_tac `([_],[],t4)`
  \\ first_x_assum (qspecl_then [`t4`,`q4`,`l4`] mp_tac)
  \\ impl_tac \\ rw [] \\ fs []
  \\ fs [let_state_rel_def]
  \\ unabbrev_all_tac \\ fs [initial_state_def]);
val _ = show "let_evaluate_Call_replay_typed" let_evaluate_Call_replay;

val let_do_app_lemma_replay = prove(
  ``let_state_rel q4 l4 s1 t1 ==>
    case do_app op a s1 of
    | Rerr err => do_app op a t1 = Rerr err
    | Rval (v,s2) => ?t2. let_state_rel q4 l4 s2 t2 /\
                          do_app op a t1 = Rval (v,t2)``,
  Cases_on `op = Install` THEN1
   (rw [] \\ fs [do_app_def]
    \\ every_case_tac \\ fs []
    \\ fs [case_eq_thms,UNCURRY,do_install_def]
    \\ rveq \\ fs [PULL_EXISTS]
    \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
    \\ fs [let_state_rel_def] \\ rveq \\ fs []
    \\ fs [state_component_equality,domain_map]
    THEN1
     (fs [shift_seq_def,o_DEF] \\ rfs []
      \\ Cases_on `s1.compile_oracle 0` \\ fs []
      \\ Cases_on `r` \\ fs [] \\ Cases_on `h` \\ fs [] \\ rveq \\ fs []
      \\ fs [map_union] \\ AP_TERM_TAC
      \\ fs [map_fromAList] \\ AP_TERM_TAC \\ fs []
      \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
      \\ fs [FUN_EQ_THM,FORALL_PROD])
    \\ CCONTR_TAC \\ fs [] \\ rfs [FORALL_PROD,shift_seq_def])
  \\ strip_tac \\ Cases_on `do_app op a s1` \\ fs []
  THEN1
   (rename1 `_ = Rval aa`
    \\ PairCases_on `aa`
    \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code) \\ fs []
    \\ fs [let_state_rel_alt]
    \\ disch_then (qspecl_then [`map (let_opt q4 l4) s1.code`,
        `t1.compile`,`(I ## MAP (I ## let_opt q4 l4)) ∘
          s1.compile_oracle`] mp_tac)
    \\ qpat_x_assum `t1 = _` (assume_tac o GSYM) \\ fs []
    \\ strip_tac \\ fs []
    \\ qpat_x_assum `_ = t1` (assume_tac o GSYM) \\ fs []
    \\ rw [] \\ fs [state_component_equality]
    \\ imp_res_tac do_app_const \\ fs [])
  \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code_err_not_Install) \\ fs []
  \\ fs [let_state_rel_alt]
  \\ disch_then (qspecl_then [`map (let_opt q4 l4) s1.code`,
      `t1.compile`,`(I ## MAP (I ##  let_opt q4 l4)) ∘
        s1.compile_oracle`] mp_tac)
  \\ qpat_x_assum `t1 = _` (assume_tac o GSYM) \\ fs []);
val _ = show "let_do_app_lemma_replay_typed" let_do_app_lemma_replay;
val _ = show "bvl_inline_cc_def_typed" bvl_inlineProofTheory.bvl_inline_cc_def;
val _ = show "bvl_inline_co_def_typed" bvl_inlineProofTheory.bvl_inline_co_def;
val _ = show "evaluate_add_clock_initial_state_typed" bvlPropsTheory.evaluate_add_clock_initial_state;
val _ = show "bvl_semantics_def_typed" bvlSemTheory.semantics_def;
