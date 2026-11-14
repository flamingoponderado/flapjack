(* Typed source statements for closure numbering correctness. *)
load "preamble";
load "clos_numberProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "renumber_def_typed=" clos_numberTheory.renumber_code_locs_def;
val _ = show "renumber_any_dests_typed=" clos_numberProofTheory.renumber_code_locs_any_dests;
val _ = show "renumber_imp_even_typed=" clos_numberProofTheory.renumber_code_locs_imp_EVEN;
val _ = show "renumber_labels_typed=" clos_numberProofTheory.renumber_code_locs_get_code_labels;
val _ = show "renumber_no_labels_typed=" clos_numberProofTheory.renumber_code_locs_no_Labels;
val _ = show "renumber_obeys_max_app_typed=" clos_numberProofTheory.renumber_code_locs_obeys_max_app;
val _ = show "lookup_vars_none_related_typed=" clos_numberProofTheory.lookup_vars_NONE_related_env;
val _ = show "lookup_vars_some_related_typed=" clos_numberProofTheory.lookup_vars_SOME_related_env;
val _ = show "compile_inc_def_typed=" clos_numberTheory.compile_inc_def;
val _ = show "make_even_def_typed=" miscTheory.make_even_def;
val _ = show "even_make_even_typed=" miscTheory.EVEN_make_even;
val _ = show "ignore_table_def_typed=" clos_numberTheory.ignore_table_def;
val _ = show "ignore_table_imp_typed=" clos_numberProofTheory.ignore_table_imp;
val _ = show "simple_state_rel_typed=" clos_numberProofTheory.simple_state_rel;
val _ = show "v_rel_rules_typed=" clos_numberProofTheory.v_rel_rules;
val _ = show "ref_rel_def_typed=" closPropsTheory.ref_rel_def;
val _ = show "fmap_rel_def_typed=" finite_mapTheory.fmap_rel_def;
val _ = show "state_rel_typed=" clos_numberProofTheory.state_rel_def;
val _ = show "renumber_correct_typed=" clos_numberProofTheory.renumber_code_locs_correct;
val _ = show "renumber_code_locs_inc_typed=" clos_numberProofTheory.renumber_code_locs_inc;
val _ = show "renumber_code_locs_imp_inc_typed=" clos_numberProofTheory.renumber_code_locs_imp_inc;
val _ = show "renumber_list_imp_length_typed=" clos_numberProofTheory.renumber_code_locs_list_IMP_LENGTH;
val _ = show "renumber_list_distinct_typed=" clos_numberProofTheory.renumber_code_locs_list_distinct;
val _ = show "renumber_distinct_typed=" clos_numberProofTheory.renumber_code_locs_distinct;
val _ = show "renumber_even_typed=" clos_numberProofTheory.renumber_code_locs_EVEN;
val _ = show "renumber_vars_none_typed=" clos_numberProofTheory.renumber_code_locs_every_Fn_vs_NONE;
val _ = show "renumber_elist_globals_typed=" clos_numberProofTheory.renumber_code_locs_elist_globals;
val _ = show "renumber_esgc_free_typed=" clos_numberProofTheory.renumber_code_locs_esgc_free;
val _ = show "every_fn_vs_none_every_typed=" closPropsTheory.every_Fn_vs_NONE_EVERY;
val _ = show "renumber_code_locs_every_Fn_SOME_typed=" clos_numberProofTheory.renumber_code_locs_every_Fn_SOME;
open closLangTheory clos_numberTheory clos_numberProofTheory closSemTheory closPropsTheory
  listTheory rich_listTheory finite_mapTheory backendPropsTheory miscTheory;
open preamble;
val state_rel_refs_replay = Q.prove(
  `state_rel s t ==> fmap_rel (ref_rel (v_rel t.max_app)) s.refs t.refs`,
  srw_tac[][state_rel_def]);
val rel_update_thunk_replay = Q.prove(
  `state_rel s1 s2 /\ LIST_REL (v_rel s1.max_app) vs ys /\
   update_thunk [RefPtr v ptr] s1.refs vs = SOME refs1 ==>
   ?refs2. update_thunk [RefPtr v ptr] s2.refs ys = SOME refs2 /\
     state_rel (s1 with refs := refs1) (s2 with refs := refs2)`,
  rw [] >>
  gvs [oneline update_thunk_def, AllCaseEqs()] >> rw [] >>
  gvs [oneline dest_thunk_def, AllCaseEqs()] >>
  (gvs [Once v_rel_cases, oneline store_thunk_def, AllCaseEqs(), PULL_EXISTS] >>
   rpt (imp_res_tac state_rel_refs_replay >> gvs [fmap_rel_def, FLOOKUP_DEF] >>
        first_x_assum dxrule >> rw [] >> gvs []) >>
   gvs [state_rel_def, fmap_rel_def, FAPPLY_FUPDATE_THM] >> rw [] >>
   simp [Once v_rel_cases] >> metis_tac []));
val _ = show "rel_update_thunk_replay_typed=" rel_update_thunk_replay;
val state_rel_max_app_replay = Q.prove(`!s t. state_rel s t ==> s.max_app = t.max_app`, srw_tac[][state_rel_def]);
val state_rel_clock_replay = Q.prove(`state_rel s t ==> s.clock = t.clock`, rw[state_rel_def]);
val state_rel_code_replay = Q.prove(`state_rel s t ==> s.code = FEMPTY /\ t.code = FEMPTY`, rw[state_rel_def]);
val v_to_bytes_replay = Q.prove(`v_rel m v w ==> v_to_bytes v = v_to_bytes w`, metis_tac [simple_val_rel, simple_val_rel_v_to_bytes]);
val v_to_words_replay = Q.prove(`v_rel m v w ==> v_to_words v = v_to_words w`, metis_tac [simple_val_rel, simple_val_rel_v_to_words]);
val _ = show "v_to_bytes_replay_typed=" v_to_bytes_replay;
val _ = show "v_to_words_replay_typed=" v_to_words_replay;
val do_install_replay = Q.prove(`state_rel s1 s2 ∧
   LIST_REL (v_rel s1.max_app) x1 x2 ⇒
   (∀err t. do_install x1 s1 = (Rerr (Rabort Rtimeout_error),t) ⇒
            ?t'. do_install x2 s2 = (Rerr (Rabort Rtimeout_error),t') /\
                 state_rel t t') ∧
   (∀e1 t1. do_install x1 s1 = (Rval e1,t1) ⇒
     ∃e2 t2. do_install x2 s2 = (Rval e2,t2) ∧
             ¬contains_App_SOME t1.max_app (e1) ∧ t1.max_app = s1.max_app ∧
             e2 = SND (compile_inc (FST(FST(s1.compile_oracle 0))) e1) ∧
             state_rel t1 t2)`,
strip_tac
  >> `∃res. do_install x1 s1 = res` by fs[]
  >> fs[do_install_def,case_eq_thms] >> rveq >> fs[]
  >> imp_res_tac v_to_bytes_replay >> fs[]
  >> imp_res_tac v_to_words_replay >> fs[]
  >> pairarg_tac >> fs[] >> pairarg_tac >> fs[]
  >> imp_res_tac state_rel_code_replay >> fs[]
  >> imp_res_tac state_rel_max_app_replay >> fs[]
  >> imp_res_tac state_rel_clock_replay >> fs[]
  >> fs[shift_seq_def]
  >> `s2.compile_oracle = state_co (ignore_table compile_inc) s1.compile_oracle` by fs[state_rel_def]
  >> `s1.compile = state_cc (ignore_table compile_inc) s2.compile` by fs[state_rel_def]
  >> fs[]
  >> qpat_x_assum`state_co _ _ _ = _`mp_tac
  >> simp[Once state_co_def]
  >> pairarg_tac >> fs[]
  >> pairarg_tac >> fs[]
  >> strip_tac >> rveq
  >> imp_res_tac ignore_table_imp >> fs[]
  >> IF_CASES_TAC >> fs[]
  >> simp[state_cc_def]
  >> CASE_TAC >> fs[]
  >> split_pair_case_tac >> fs[] >> rveq
  >> simp[FST_state_co]
  >> split_pair_case_tac >> fs[] >> rveq
  >> split_pair_case_tac >> fs[] >> rveq
  >> IF_CASES_TAC >> fs[]
  >> fs[CaseEq"bool"]
  >> fs[ignore_table_def]
  >> pairarg_tac >> fs[] >> rveq
  >> rename [`_ = (st1,code1)`]
  >> `code1 <> []` by
    (fs [compile_inc_def] >> pairarg_tac >> fs [] >> rveq >> fs [])
  >> fs[state_rel_def,state_co_def,ignore_table_def]
  >> fs[FUPDATE_LIST_THM]
  >> metis_tac[FUPDATE_LIST_THM,FST,SND,DECIDE``(n+1n)+1 = n+2``,LENGTH_NIL]);
val _ = show "do_install_replay_typed=" do_install_replay;
val dest_closure_v_rel_none_replay = Q.prove(
  `!f args f' args'.
    v_rel max_app f f' /\ LIST_REL (v_rel max_app) args args' /\
    dest_closure max_app NONE f args = NONE ==>
    dest_closure max_app NONE f' args' = NONE`,
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[dest_closure_def, v_rel_cases] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[LET_THM, check_loc_def] >>
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  srw_tac[][] >>
  TRY decide_tac >>
  Cases_on `EL k es` >>
  full_simp_tac(srw_ss())[] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `renumber_code_locs_list n (MAP SND es)` >>
  imp_res_tac renumber_code_locs_list_length >>
  srw_tac[][] >>
  Cases_on `EL k (ZIP (MAP FST es,r'))` >>
  srw_tac[][] >>
  CCONTR_TAC >>
  full_simp_tac(srw_ss())[] >>
  `k < LENGTH es` by decide_tac >>
  `LENGTH (MAP FST es) = LENGTH r'` by metis_tac [LENGTH_MAP] >>
  full_simp_tac(srw_ss())[EL_ZIP, EL_MAP] >>
  srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[]);
val _ = show "dest_closure_v_rel_none_replay_typed=" dest_closure_v_rel_none_replay;
val _ = show "semantics_number_typed=" clos_numberProofTheory.semantics_number;
