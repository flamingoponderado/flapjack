load "preamble"; load "clos_interpProofTheory";
open HolKernel Parse boolLib bossLib;
open preamble closLangTheory closSemTheory closPropsTheory clos_interpTheory;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "every_Fn_vs_NONE_insert_interp_typed=" clos_interpProofTheory.every_Fn_vs_NONE_insert_interp;
val _ = show_thm "contains_App_SOME_insert_interp_typed=" clos_interpProofTheory.contains_App_SOME_insert_interp;
val opt_interp_lemma_replay = Q.prove (
  `opt_interp x = SOME x' ⇒
   set_globals x' = {||} ∧ set_globals x = {||} ∧
   (1 ≤ max_app ⇒ ¬contains_App_SOME max_app [x']) ∧
   every_Fn_vs_NONE [x'] ∧ no_mti x' ∧ esgc_free x ∧ esgc_free x'`,
  strip_tac \\ gvs [opt_interp_def,AllCaseEqs()] \\
  fs [no_mti_def,contains_App_SOME_def,op_gbag_def] \\
  qsuff_tac `
    (∀x. can_interpret x ⇒ set_globals x = {||} ∧ esgc_free x) ∧
    (∀x. can_interpret_list x ⇒ elist_globals x = {||} ∧ EVERY esgc_free x)`
  >- (rw [] \\ res_tac \\ fs []) \\
  rpt $ pop_assum kall_tac \\
  Induct \\ fs [can_interpret_def] \\
  Cases \\ fs [can_interpret_op_def,op_gbag_def] \\
  Cases_on `g` \\ fs [can_interpret_op_def,op_gbag_def]);
val _ = show_thm "opt_interp_lemma_replay_typed=" opt_interp_lemma_replay;
val has_install_list_eq_replay = Q.prove (
  `∀xs. has_install_list xs ⇔ EXISTS has_install xs`,
  Induct \\ fs [has_install_def]);
val _ = show_thm "has_install_list_eq_replay_typed=" has_install_list_eq_replay;
val lookup_vars_ok_replay = Q.prove (
  `∀vs env env'. lookup_vars vs env = SOME env' ∧ EVERY v_ok env ⇒ EVERY v_ok env'`,
  Induct \\ fs [lookup_vars_def] \\
  rw [] \\ gvs [AllCaseEqs()] \\
  res_tac \\ fs [] \\
  gvs [EVERY_EL]);
val _ = show_thm "lookup_vars_ok_replay_typed=" lookup_vars_ok_replay;
val _ = show_thm "state_rel_prime_def_typed=" clos_interpProofTheory.state_rel'_def;
val state_rel_prime_dec_clock_replay = Q.prove (
  `state_rel' s t ⇒ state_rel' (dec_clock 1 s) (dec_clock 1 t)`,
  gvs [clos_interpProofTheory.state_rel'_def, dec_clock_def]);
val _ = show_thm "state_rel_prime_dec_clock_replay_typed=" state_rel_prime_dec_clock_replay;
val state_rel_prime_clock_replay = Q.prove (
  `state_rel' s t ⇒ t.clock = s.clock`,
  fs [clos_interpProofTheory.state_rel'_def]);
val _ = show_thm "state_rel_prime_clock_replay_typed=" state_rel_prime_clock_replay;
val state_rel_prime_refs_replay = Q.prove (
  `state_rel' s t ⇒ t.refs = s.refs`,
  fs [clos_interpProofTheory.state_rel'_def]);
val _ = show_thm "state_rel_prime_refs_replay_typed=" state_rel_prime_refs_replay;
val _ = show_thm "evaluate_change_oracle_typed=" clos_interpProofTheory.evaluate_change_oracle;
val _ = show_thm "state_rel_def_typed=" clos_interpProofTheory.state_rel_def;
val _ = show_thm "state_rel_1_def_typed=" clos_interpProofTheory.state_rel_1_def;
val _ = show_thm "evaluate_interp_lemma_typed=" clos_interpProofTheory.evaluate_interp_lemma;
val _ = show_thm "evaluate_interp_thm_typed=" clos_interpProofTheory.evaluate_interp_thm;
val state_rel_refs_clocks_replay = Q.prove (
  `state_rel s1 s2 ⇒ s1.refs = s2.refs ∧ s1.clock = s2.clock`,
  rw [clos_interpProofTheory.state_rel_def, state_component_equality]);
val _ = show_thm "state_rel_refs_clocks_replay_typed=" state_rel_refs_clocks_replay;
val state_rel_update_thunk_replay = Q.prove (
  `state_rel s1 s2 ⇒
     update_thunk [RefPtr v ptr] s1.refs vs = SOME refs1 ⇒
       ∃refs2. update_thunk [RefPtr v ptr] s2.refs vs = SOME refs2 ∧
         state_rel (s1 with refs := refs1) (s2 with refs := refs2)`,
  rw [] \\
  gvs [oneline update_thunk_def, AllCaseEqs()] \\ rw [] \\
  gvs [oneline dest_thunk_def, AllCaseEqs()] \\
  (gvs [oneline store_thunk_def, AllCaseEqs()] \\
   imp_res_tac state_rel_refs_clocks_replay \\ gvs [] \\
   gvs [clos_interpProofTheory.state_rel_def]));
val _ = show_thm "state_rel_update_thunk_replay_typed=" state_rel_update_thunk_replay;
val _ = show_thm "interp_assum_def_typed=" clos_interpProofTheory.interp_assum_def;
val _ = show_thm "interp_assum_leq_typed=" clos_interpProofTheory.interp_assum_leq;
val _ = show_thm "evaluate_insert_interp1_typed=" clos_interpProofTheory.evaluate_insert_interp1;
val _ = show_thm "evaluate_insert_interp_typed=" clos_interpProofTheory.evaluate_insert_interp;
val _ = show_thm "opt_interp_thm_typed=" clos_interpProofTheory.opt_interp_thm;
val _ = show_thm "opt_interp1_thm_prime_typed=" clos_interpProofTheory.opt_interp1_thm';
val _ = show_thm "opt_interp1_thm_typed=" clos_interpProofTheory.opt_interp1_thm;
val _ = show_thm "clos_interpreter_correct_typed=" clos_interpProofTheory.clos_interpreter_correct;
val _ = show_thm "clos_interp_rev_thm_typed=" clos_interpProofTheory.clos_interp_rev_thm;
val _ = show_thm "clos_interp_el_thm_typed=" clos_interpProofTheory.clos_interp_el_thm;
val evaluate_Constant_replay = Q.prove (
  `evaluate ([Op t (BlockOp (Constant c)) []],env,s) = (Rval [make_const c],s)`,
  fs [evaluate_def,do_app_def]);
val _ = show_thm "evaluate_Constant_replay_typed=" evaluate_Constant_replay;
val _ = show_thm "evaluate_Cons_nil_typed=" clos_interpProofTheory.evaluate_Cons_nil;
val _ = show_thm "evaluate_Global_0_typed=" clos_interpProofTheory.evaluate_Global_0;
val _ = show_thm "v_to_list_list_to_v_typed=" clos_interpProofTheory.v_to_list_list_to_v;
