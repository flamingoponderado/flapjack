load "source_to_flatProofTheory";
load "preamble";
load "experimentalLib";
open HolKernel Parse boolLib bossLib source_to_flatProofTheory source_to_flatTheory;
val _ = Globals.linewidth := 1000000;
val s_i1 = ``s_i1 : ('f_orac_st, 'ffi) flatSem$state``;
val theorem_statement = ``
(!cenv s p v env r env' env'' env_i1 ^s_i1 v_i1 st'.
   semanticPrimitives$pmatch cenv s p v env = r ∧
   s_rel genv st' s_i1 ∧
   global_env_inv genv comp_map2 shadowers senv ∧
   genv_c_ok genv.c ∧
   genv_c_tys_ok genv.c genv.tys ∧
   cenv = senv.c ∧
   comp_map2.c = comp_map.c ∧
   env = env' ++ env'' ∧
   s_i1.globals = genv.v ∧
   s = st'.refs ∧
   v_rel genv v v_i1 ∧
   env_rel genv (alist_to_ns env') env_i1
   ⇒
   ?r_i1.
     flatSem$pmatch s_i1 (compile_pat comp_map p) v_i1 env_i1 = r_i1 ∧
     match_result_rel genv env'' r r_i1) ∧
  (!cenv s ps vs env r env' env'' env_i1 ^s_i1 vs_i1 st'.
   semanticPrimitives$pmatch_list cenv s ps vs env = r ∧
   global_env_inv genv comp_map2 shadowers senv ∧
   genv_c_ok genv.c ∧
   genv_c_tys_ok genv.c genv.tys ∧
   cenv = senv.c ∧
   comp_map2.c = comp_map.c ∧
   env = env' ++ env'' ∧
   s_i1.globals = genv.v ∧
   s_rel genv st' s_i1 ∧
   s = st'.refs ∧
   LIST_REL (v_rel genv) vs vs_i1 ∧
   env_rel genv (alist_to_ns env') env_i1
   ⇒
   ?r_i1.
     flatSem$pmatch_list s_i1 (MAP (compile_pat comp_map) ps) vs_i1 env_i1 = r_i1 ∧
     match_result_rel genv env'' r r_i1)
``;
val _ = (print "pmatch_statement_typed="; Lib.with_flag (Globals.show_types,true) print_term theorem_statement);

(* Reconstruct the local value equations and replay the original local proof. *)
open semanticPrimitivesTheory flatSemTheory
  namespaceTheory namespacePropsTheory listTheory rich_listTheory alistTheory
  arithmeticTheory pairTheory optionTheory pred_setTheory;
open preamble;
open experimentalLib;
val eta2 = prove (``!f x. (\y. f x y) = f x``, metis_tac []);
val NOT_NULL_EQ = prove (``(~ NULL xs) = (?y ys. xs = CONS y ys)``, Cases_on `xs` >> simp []);
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val v_rel_eqns =
  [``v_rel genv (Litv l) v``, ``v_rel genv (Conv cn vs) v``,
   ``v_rel genv (Loc b l) v``, ``v_rel genv (Vectorv vs) v``,
   ``env_rel genv nsEmpty env'``, ``env_rel genv (nsBind x v env) env'``,
   ``v_rel genv (Env e id) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases]) |> map GEN_ALL |> LIST_CONJ;
val pmatch_replay = prove (theorem_statement,
  ho_match_mp_tac semanticPrimitivesTheory.pmatch_ind >>
  srw_tac[][semanticPrimitivesTheory.pmatch_def, flatSemTheory.pmatch_def, compile_pat_def] >>
  full_simp_tac(srw_ss())[match_result_rel_def, flatSemTheory.pmatch_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH
  >- (fs[compile_pat_def, v_rel_eqns] >> rveq >> fs[pmatch_def] >>
    TOP_CASE_TAC >- simp [match_result_rel_def] >>
    fs [] >>
    qmatch_assum_rename_tac `nsLookup _ _ = SOME p` >>
    `?l stamp. p = (l, stamp)` by metis_tac [pair_CASES] >> fs [] >>
    TOP_CASE_TAC >> simp [match_result_rel_def] >>
    fs [v_rel_global_eqn] >>
    last_assum (drule_then strip_assume_tac) >>
    rfs [eta2] >>
    drule_then (drule_then (fn t => CHANGED_TAC (DEP_REWRITE_TAC [t])))
        genv_c_ok_pmatch_stamps_ok >>
    simp [] >>
    TOP_CASE_TAC >> simp [match_result_rel_def]
    >- (
      (* same ctor *)
      TOP_CASE_TAC >> simp [match_result_rel_def] >>
      rw [] >>
      fs [semanticPrimitivesTheory.same_ctor_def, genv_c_ok_def] >>
      metis_tac [genv_c_ok_def, FST]
    )
    >- (
      (* diff ctor *)
      fs [] >>
      rw [match_result_rel_def] >>
      drule_then (drule_then (drule_then drule))
        genv_c_ok_same_type_FST_eq_imp_same_ctor >>
      simp []
    )
  )
  >- (simp [pmatch_stamps_ok_cases] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def, s_rel_cases] >>
      metis_tac [])
  >- (imp_res_tac s_rel_cases >>
      imp_res_tac NOT_NULL_EQ >>
      full_simp_tac(srw_ss())[store_lookup_def, ADD1, REWRITE_RULE [ADD1] EL] >>
      imp_res_tac LIST_REL_LENGTH >>
      rw [match_result_rel_def] >>
      fs [] >>
      imp_res_tac LIST_REL_IMP_EL2 >>
      fs [sv_rel_cases, match_result_rel_def]
  )
  >- (
    gvs []
    \\ ‘((i,v)::(env' ++ env'')) = ((i,v)::env') ++ env''’
      by gs []
    \\ pop_assum SUBST_ALL_TAC
    \\ first_x_assum irule \\ gs []
    \\ simp [env_rel_bind_one])
  >- (
      rfs [] >>
      first_x_assum (qsubterm_then
          `pmatch _ (compile_pat _ _) _ _` mp_tac) >>
      rpt (disch_then (first_assum o mp_then Any mp_tac)) >>
      rw [] >>
      imp_res_tac match_result_rel_imp >> fs [match_result_rel_def] >>
      rpt (first_x_assum (first_assum o mp_then Any strip_assume_tac)) >>
      fs [] >>
      imp_res_tac match_result_rel_imp >> fs [match_result_rel_def]
  ));

val _ = if null (hyp pmatch_replay) then () else raise Fail "pmatch replay has hypotheses";
val _ = (print "\npmatch_replay_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl pmatch_replay); print "\n");
