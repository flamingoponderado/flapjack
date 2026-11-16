(* Replay environment-conversion declarations and initialization facts from
   envRelScript.sml and repl_typesScript.sml without building those theories. *)
load "inferPropsTheory";
load "namespacePropsTheory";
load "primTypesTheory";
load "typeSysPropsTheory";
load "semanticPrimitivesTheory";
load "preamble";
open HolKernel Parse boolLib bossLib;
open preamble inferPropsTheory inferTheory typeSystemTheory primTypesTheory semanticPrimitivesTheory;
val _ = new_theory "flapjack_env_rel_init_replay";
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = Datatype `probe_store_t = ProbeRef_t t | ProbeW8array_t | ProbeVarray_t t`;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val probe_tenv_to_ienv_def = Define `
  probe_tenv_to_ienv tenv =
    <| inf_v := nsMap (\(tvs, t). (tvs, unconvert_t t)) tenv.v;
       inf_c := tenv.c;
       inf_t := tenv.t |>`;
val _ = show "tenv_to_ienv_replay_typed" probe_tenv_to_ienv_def;

val _ = show "lift_ienv_typed" inferTheory.lift_ienv_def;
val _ = show "loc_err_info_axiom_typed" (TypeBase.axiom_of ``:loc_err_info``);
val _ = show "failwith_typed" inferTheory.failwith_def;
val _ = show "guard_typed" inferTheory.guard_def;
val _ = show "infer_read_typed" inferTheory.read_def;
val _ = show "infer_write_typed" inferTheory.write_def;
val _ = show "lookup_st_ex_typed" inferTheory.lookup_st_ex_def;
val _ = show "id_to_string_typed" infer_tTheory.id_to_string_def;
val _ = show "infer_st_axiom_typed" (TypeBase.axiom_of ``:infer_st``);
val _ = show "init_infer_state_typed" inferTheory.init_infer_state_def;
val _ = show "init_state_typed" inferTheory.init_state_def;
val _ = show "fresh_uvar_typed" inferTheory.fresh_uvar_def;
val _ = show "n_fresh_uvar_typed" inferTheory.n_fresh_uvar_def;
val _ = show "n_fresh_id_typed" inferTheory.n_fresh_id_def;
val _ = show "get_next_uvar_typed" inferTheory.get_next_uvar_def;
val _ = show "add_constraint_typed" inferTheory.add_constraint_def;
val _ = show "add_constraints_typed" inferTheory.add_constraints_def;
val _ = show "apply_subst_typed" inferTheory.apply_subst_def;
val _ = show "apply_subst_list_typed" inferTheory.apply_subst_list_def;
val _ = show "extend_dec_ienv_typed" inferTheory.extend_dec_ienv_def;
val _ = show "nsLookup_nsMap_typed" namespacePropsTheory.nsLookup_nsMap;
val _ = show "nsLookupMod_nsMap_typed" namespacePropsTheory.nsLookupMod_nsMap;
val _ = show "nsAll_nsMap_typed" namespacePropsTheory.nsAll_nsMap;
val _ = show "nsAll_nsLift_typed" namespacePropsTheory.nsAll_nsLift;
val _ = show "ienv_ok_lift_typed" inferPropsTheory.ienv_ok_lift;
val _ = show "ienv_ok_extend_dec_ienv_typed" inferPropsTheory.ienv_ok_extend_dec_ienv;
val _ = show "extend_dec_tenv_ok_typed" typeSysPropsTheory.extend_dec_tenv_ok;

val tenv_to_ienv_lift_replay = Q.prove(
  `!mn tenv. probe_tenv_to_ienv (tenvLift mn tenv) =
     lift_ienv mn (probe_tenv_to_ienv tenv)`,
  rw [probe_tenv_to_ienv_def, lift_ienv_def, tenvLift_def,
      namespacePropsTheory.nsLift_nsMap]);
val _ = show "tenv_to_ienv_lift_replay_typed" tenv_to_ienv_lift_replay;

val tenv_to_ienv_extend_replay = Q.prove(
  `!tenv1 tenv2. probe_tenv_to_ienv (extend_dec_tenv tenv2 tenv1) =
     extend_dec_ienv (probe_tenv_to_ienv tenv2) (probe_tenv_to_ienv tenv1)`,
  rw [probe_tenv_to_ienv_def, extend_dec_tenv_def, extend_dec_ienv_def,
      namespacePropsTheory.nsMap_nsAppend]);
val _ = show "tenv_to_ienv_extend_replay_typed" tenv_to_ienv_extend_replay;

val check_freevars_to_check_t_replay = Q.prove(
  `!t z. check_freevars n [] t ==> check_t n {} (unconvert_t t)`,
  ho_match_mp_tac unconvert_t_ind >> rw [] >>
  fs [unconvert_t_def, check_freevars_def, check_t_def] >>
  fs [EVERY_MAP, EVERY_MEM]);
val _ = show "check_freevars_to_check_t_replay_typed" check_freevars_to_check_t_replay;

val probe_convert_t_def = tDefine "probe_convert_t" `
  (probe_convert_t (Infer_Tvar_db n) = Tvar_db n) ∧
  (probe_convert_t (Infer_Tapp ts tc) = Tapp (MAP probe_convert_t ts) tc)`
  (WF_REL_TAC `measure infer_t_size` >> rw [] >>
   induct_on `ts` >> rw [infer_tTheory.infer_t_size_def] >> res_tac >> decide_tac);
val _ = show "convert_t_replay_typed" probe_convert_t_def;

val probe_ienv_to_tenv_def = Define `
  probe_ienv_to_tenv ienv =
    <| v := nsMap (\(tvs, t). (tvs, probe_convert_t t)) ienv.inf_v;
       c := ienv.inf_c;
       t := ienv.inf_t |>`;
val _ = show "ienv_to_tenv_replay_typed" probe_ienv_to_tenv_def;

val _ = show "infer_deBruijn_inc_typed" inferTheory.infer_deBruijn_inc_def;

val convert_inc_replay = Q.prove(
  `!t tvs tvs'. check_t tvs' {} t ⇒
     probe_convert_t (infer_deBruijn_inc tvs t) = deBruijn_inc 0 tvs (probe_convert_t t)`,
  ho_match_mp_tac (fetch "-" "probe_convert_t_ind") >>
  rw [check_t_def, probe_convert_t_def, infer_deBruijn_inc_def, deBruijn_inc_def] >>
  induct_on `ts` >> fs [] >> metis_tac []);
val _ = show "convert_inc_replay_typed" convert_inc_replay;

val inc_convert_t_replay = Q.prove(
  `(!t tvs' tvs. check_t tvs' {} t ⇒ deBruijn_inc tvs' tvs (probe_convert_t t) = probe_convert_t t) ∧
   (!ts tvs' tvs. EVERY (check_t tvs' {}) ts ⇒
      MAP (deBruijn_inc tvs' tvs o probe_convert_t) ts = MAP probe_convert_t ts)`,
  ho_match_mp_tac infer_tTheory.infer_t_induction >>
  rw [check_t_def, probe_convert_t_def, deBruijn_inc_def] >> metis_tac [MAP_MAP_o]);
val _ = show "inc_convert_t_replay_typed" inc_convert_t_replay;

val deBruijn_subst_convert_replay = Q.prove(
  `(∀t. check_t n {} t ⇒
      deBruijn_subst 0 (MAP probe_convert_t subst) (probe_convert_t t) =
      probe_convert_t (infer_deBruijn_subst subst t)) ∧
   (∀ts. EVERY (check_t n {}) ts ⇒
      MAP ((deBruijn_subst 0 (MAP probe_convert_t subst)) o probe_convert_t) ts =
      MAP (probe_convert_t o (infer_deBruijn_subst subst)) ts)`,
  ho_match_mp_tac infer_tTheory.infer_t_induction >>
  rw [check_t_def] >>
  fs [probe_convert_t_def, deBruijn_subst_def, infer_deBruijn_subst_alt] >-
    (IF_CASES_TAC >> fs [EL_MAP, probe_convert_t_def]) >>
  fs [MAP_MAP_o, EVERY_MEM, MAP_EQ_f]);
val _ = show "deBruijn_subst_convert_replay_typed" deBruijn_subst_convert_replay;

val convert_t_subst_replay = Q.prove(
  `(!t tvs ts'. LENGTH tvs = LENGTH ts' ∧ check_freevars 0 tvs t ⇒
      probe_convert_t (infer_type_subst (ZIP (tvs,ts')) t) =
      type_subst (alist_to_fmap (ZIP (tvs, MAP probe_convert_t ts'))) t) ∧
   (!ts tvs ts'. LENGTH tvs = LENGTH ts' ∧ EVERY (check_freevars 0 tvs) ts ⇒
      MAP probe_convert_t (MAP (infer_type_subst (ZIP (tvs,ts'))) ts) =
      MAP (type_subst (alist_to_fmap (ZIP (tvs, MAP probe_convert_t ts')))) ts)`,
  ho_match_mp_tac t_induction >>
  rw [check_freevars_def, probe_convert_t_def, type_subst_def, infer_type_subst_alt] >|
  [full_case_tac >> full_case_tac >> fs [ALOOKUP_FAILS] >>
   imp_res_tac ALOOKUP_MEM >> REPEAT (pop_assum mp_tac) >> rw [MAP_ZIP] >>
   REPEAT (pop_assum mp_tac) >> Q.SPEC_TAC (`tvs`,`tvs`) >> induct_on `ts'` >>
   rw [] >> cases_on `tvs` >> fs [] >> metis_tac [optionTheory.SOME_11],
   metis_tac []]);
val _ = show "convert_t_subst_replay_typed" convert_t_subst_replay;

val db_subst_infer_subst_swap3_replay = Q.prove(
  `!t tvs s subst. t_wfs s ∧ check_freevars tvs [] t ⇒
    probe_convert_t (t_walkstar s (infer_deBruijn_subst subst (unconvert_t t))) =
    deBruijn_subst 0 (MAP (probe_convert_t o t_walkstar s) subst) t`,
  ho_match_mp_tac unconvert_t_ind >>
  rw [unconvert_t_def, infer_deBruijn_subst_alt, deBruijn_subst_def,
      check_freevars_def, probe_convert_t_def, unifyTheory.t_walkstar_eqn1] >-
    rw [EL_MAP] >>
  rw [MAP_MAP_o, combinTheory.o_DEF] >>
  rw [MAP_EQ_f] >> first_x_assum drule >>
  fs [EVERY_MEM] >> metis_tac []);
val _ = show "db_subst_infer_subst_swap3_replay_typed" db_subst_infer_subst_swap3_replay;

val check_convert_freevars_replay = Q.prove(
  `!tvs uvs t. check_t tvs uvs t ⇒ (uvs = {}) ⇒ check_freevars tvs [] (probe_convert_t t)`,
  ho_match_mp_tac check_t_ind >>
  rw [check_freevars_def, check_t_def, probe_convert_t_def] >>
  fs [EVERY_MEM, MEM_MAP] >> metis_tac []);
val _ = show "check_convert_freevars_replay_typed" check_convert_freevars_replay;

val check_t_to_check_freevars_replay = Q.prove(
  `!tvs (n:num set) t. check_t tvs {} t ⇒ check_freevars tvs [] (probe_convert_t t)`,
  ho_match_mp_tac check_t_ind >>
  rw [check_t_def, check_freevars_def, probe_convert_t_def, EVERY_MAP] >>
  fs [EVERY_MEM]);
val _ = show "check_t_to_check_freevars_replay_typed" check_t_to_check_freevars_replay;

val check_t_empty_unconvert_convert_id_replay = Q.prove(
  `!t n. check_t n {} t ⇒ unconvert_t (probe_convert_t t) = t`,
  ho_match_mp_tac (fetch "-" "probe_convert_t_ind") >>
  rw [] >> fs [unconvert_t_def, probe_convert_t_def, check_t_def] >>
  fs [MAP_MAP_o, MAP_EQ_ID, EVERY_MEM] >> metis_tac []);
val _ = show "check_t_empty_unconvert_convert_id_replay_typed"
  check_t_empty_unconvert_convert_id_replay;

val check_freevars_empty_convert_unconvert_id_replay = Q.prove(
  `!t. check_freevars n [] t ⇒ probe_convert_t (unconvert_t t) = t`,
  ho_match_mp_tac unconvert_t_ind >>
  rw [] >> fs [unconvert_t_def, probe_convert_t_def, check_freevars_def] >>
  fs [MAP_MAP_o, MAP_EQ_ID, EVERY_MEM]);
val _ = show "check_freevars_empty_convert_unconvert_id_replay_typed"
  check_freevars_empty_convert_unconvert_id_replay;

val unconvert_db_subst_replay = Q.prove(
  `!t subst fvs l. check_freevars l [] t ⇒
    unconvert_t (deBruijn_subst 0 subst t) =
    infer_deBruijn_subst (MAP unconvert_t subst) (unconvert_t t)`,
  ho_match_mp_tac t_ind >>
  rw [deBruijn_subst_def, unconvert_t_def, infer_deBruijn_subst_alt,
      check_freevars_def, EL_MAP] >>
  irule LIST_EQ >> rw [EL_MAP] >> fs [EVERY_MEM, MEM_EL] >> metis_tac []);
val _ = show "unconvert_db_subst_replay_typed" unconvert_db_subst_replay;

val infer_type_subst_nil_replay = Q.prove(
  `(∀t. check_freevars n [] t ⇒ infer_type_subst [] t = unconvert_t t) ∧
   (∀ts. EVERY (check_freevars n []) ts ⇒ MAP (infer_type_subst []) ts = MAP unconvert_t ts)`,
  ho_match_mp_tac (TypeBase.induction_of ``:t``) >>
  rw [infer_type_subst_alt, unconvert_t_def, check_freevars_def] >>
  fsrw_tac [boolSimps.ETA_ss] []);
val _ = show "infer_type_subst_nil_replay_typed" infer_type_subst_nil_replay;

val _ = show "db_subst_inc_id_typed" inferPropsTheory.db_subst_inc_id;
val _ = show "infer_deBruijn_subst_twice_typed" inferPropsTheory.infer_deBruijn_subst_twice;
val _ = show "check_t_more2_typed" inferPropsTheory.check_t_more2;
val _ = show "deBruijn_subst_nothing_typed" inferPropsTheory.deBruijn_subst_nothing;

val probe_tscheme_approx_def = Define `
  probe_tscheme_approx max_tvs s (tvs,t) (tvs',t') ⇔
    ∃subst'. LENGTH subst' = tvs' ∧
      EVERY (check_t (max_tvs + tvs) (FDOM s)) subst' ∧
      ∀subst. LENGTH subst = tvs ⇒
        t_walkstar s (infer_deBruijn_subst subst t) =
        t_walkstar s (infer_deBruijn_subst (MAP (infer_deBruijn_subst subst) subst') t')`;
val _ = show "tscheme_approx_replay_typed" probe_tscheme_approx_def;

val probe_env_rel_sound_def = Define `
  probe_env_rel_sound s ienv tenv tenvE ⇔
    ienv.inf_t = tenv.t ∧ ienv.inf_c = tenv.c ∧
    ∀x ts. nsLookup ienv.inf_v x = SOME ts ⇒
      ∃tvs' t'. check_freevars (tvs' + num_tvs tenvE) [] t' ∧
        lookup_var x tenvE tenv = SOME (tvs', t') ∧
        probe_tscheme_approx (num_tvs tenvE) s ts (tvs', unconvert_t t')`;
val _ = show "env_rel_sound_replay_typed" probe_env_rel_sound_def;

val probe_env_rel_complete_def = Define `
  probe_env_rel_complete s ienv tenv tenvE ⇔
    ienv.inf_t = tenv.t ∧ ienv.inf_c = tenv.c ∧
    ∀x tvs t. lookup_var x tenvE tenv = SOME (tvs, t) ⇒
      (∃n. check_freevars n [] t) ∧
      ∃tvs' t'. nsLookup ienv.inf_v x = SOME (tvs',t') ∧
        probe_tscheme_approx (num_tvs tenvE) s (tvs,unconvert_t t) (tvs',t')`;
val _ = show "env_rel_complete_replay_typed" probe_env_rel_complete_def;

val probe_env_rel_def = Define `
  probe_env_rel tenv ienv ⇔
    ienv_ok {} ienv ∧ typeSoundInvariants$tenv_ok tenv ∧
    (∀x. nsLookupMod ienv.inf_v x = NONE ⇔ nsLookupMod tenv.v x = NONE) ∧
    probe_env_rel_sound FEMPTY ienv tenv Empty ∧
    probe_env_rel_complete FEMPTY ienv tenv Empty`;
val _ = show "env_rel_replay_typed" probe_env_rel_def;

val tscheme_approx_refl_replay = Q.prove(
  `!max_tvs s tvs t. probe_tscheme_approx max_tvs s (tvs,t) (tvs,t)`,
  rw [probe_tscheme_approx_def] >>
  qexists_tac `MAP Infer_Tvar_db (COUNT_LIST tvs)` >>
  rw [LENGTH_COUNT_LIST, EVERY_MAP, every_count_list, check_t_def,
      MAP_MAP_o, combinTheory.o_DEF, infer_deBruijn_subst_alt] >>
  irule (METIS_PROVE [] ``y = y' ⇒ f x y = f x y'``) >>
  irule (METIS_PROVE [] ``y = y' ⇒ f y x = f y' x``) >>
  irule LIST_EQ >> rw [LENGTH_COUNT_LIST, EL_MAP, EL_COUNT_LIST]);
val _ = show "tscheme_approx_refl_replay_typed" tscheme_approx_refl_replay;

val tscheme_approx_trans_replay = Q.prove(
  `probe_tscheme_approx max_tvs s (tvs1,t1) (tvs2,t2) ∧
   probe_tscheme_approx 0 s (tvs2,t2) (tvs3,t3) ⇒
   probe_tscheme_approx max_tvs s (tvs1,t1) (tvs3,t3)`,
  rw [probe_tscheme_approx_def] >>
  qexists_tac `MAP (infer_deBruijn_subst subst') subst''` >>
  simp [] >>
  conj_asm1_tac >-
    (fs [EVERY_MAP, EVERY_MEM] >> rw [] >>
     irule check_t_infer_deBruijn_subst >> rw [EVERY_MEM] >>
     first_x_assum drule >> metis_tac [check_t_more2, ADD_ASSOC, ADD_COMM]) >>
  rw [MAP_MAP_o] >> AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  irule (GSYM (CONJUNCT2 infer_deBruijn_subst_twice)) >>
  qexists_tac `FDOM s` >> metis_tac [check_t_more2, ADD_COMM, ADD_ASSOC]);
val _ = show "tscheme_approx_trans_replay_typed" tscheme_approx_trans_replay;

val tscheme_inst_to_approx_replay = Q.prove(
  `tscheme_inst (tvs,t) (tvs',t') ⇒
   probe_tscheme_approx 0 FEMPTY (tvs,unconvert_t t) (tvs',unconvert_t t')`,
  rw [tscheme_inst_def, probe_tscheme_approx_def, unifyTheory.t_walkstar_FEMPTY] >>
  qexists_tac `MAP unconvert_t subst` >>
  rw [EVERY_MAP] >-
    (fs [EVERY_MEM] >> metis_tac [check_freevars_to_check_t_replay]) >>
  rw [MAP_MAP_o, combinTheory.o_DEF] >>
  drule unconvert_db_subst_replay >> rw [] >>
  drule check_freevars_to_check_t_replay >> rw [] >>
  `check_t (LENGTH (MAP unconvert_t subst)) {} (unconvert_t t')` by rw [] >>
  `check_t (LENGTH (MAP unconvert_t subst)) uvs (unconvert_t t')` by metis_tac [check_t_more] >>
  drule (GEN_ALL (CONJUNCT1 infer_deBruijn_subst_twice)) >>
  rw [MAP_MAP_o, combinTheory.o_DEF]);
val _ = show "tscheme_inst_to_approx_replay_typed" tscheme_inst_to_approx_replay;

val _ = print "env_rel_tenv_to_ienv_statement_typed=";
val _ = print_term (Parse.Term `!tenv. typeSoundInvariants$tenv_ok tenv ⇒
  probe_env_rel tenv (probe_tenv_to_ienv tenv)`);
val _ = print "\n";

val _ = print "env_rel_ienv_to_tenv_statement_typed=";
val _ = print_term (Parse.Term `!ienv. ienv_ok {} ienv ⇒
  probe_env_rel (probe_ienv_to_tenv ienv) ienv`);
val _ = print "\n";

val _ = print "env_rel_extend_statement_typed=";
val _ = print_term (Parse.Term `!tenv1 ienv1 tenv2 ienv2.
  probe_env_rel tenv1 ienv1 ∧ probe_env_rel tenv2 ienv2 ⇒
  probe_env_rel (extend_dec_tenv tenv1 tenv2) (extend_dec_ienv ienv1 ienv2)`);
val _ = print "\n";

val _ = print "env_rel_empty_statement_typed=";
val _ = print_term (Parse.Term `probe_env_rel
  <| v := nsEmpty; c := nsEmpty; t := nsEmpty |>
  <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |>`);
val _ = print "\n";

val lookup_var_empty_replay = Q.prove(
  `lookup_var x (bind_tvar tvs Empty) tenv = lookup_var x Empty tenv`,
  rw [bind_tvar_def, lookup_var_def, lookup_varE_def] >>
  EVERY_CASE_TAC >> fs [tveLookup_def]);
val _ = show "lookup_var_empty_replay_typed" lookup_var_empty_replay;

val _ = print "env_rel_complete_bind_statement_typed=";
val _ = print_term (Parse.Term `probe_env_rel_complete FEMPTY ienv tenv Empty ⇒
  probe_env_rel_complete FEMPTY ienv tenv (bind_tvar tvs Empty)`);
val _ = print "\n";

val probe_set_ids_def = Define `probe_set_ids n1 (n2:num) = {m | n1 ≤ m ∧ m < n2}`;
val _ = show "set_ids_replay_typed" probe_set_ids_def;

val set_ids_eq_replay = Q.prove(
  `probe_set_ids n1 n2 = set (GENLIST (λx. x + n1) (n2-n1))`,
  fs [probe_set_ids_def, EXTENSION, MEM_MAP, MEM_GENLIST] >>
  rw [EQ_IMP_THM] >> qexists_tac `x-n1` >> fs []);
val _ = show "set_ids_eq_replay_typed" set_ids_eq_replay;

val set_ids_same_replay = Q.prove(`probe_set_ids x x = {}`,
  rw [set_ids_eq_replay]);
val _ = show "set_ids_same_replay_typed" set_ids_same_replay;

val set_ids_eq_union_replay = Q.prove(
  `x ≤ y ∧ y ≤ z ⇒ probe_set_ids x z = probe_set_ids x y ∪ probe_set_ids y z`,
  fs [probe_set_ids_def, EXTENSION]);
val _ = show "set_ids_eq_union_replay_typed" set_ids_eq_union_replay;

val set_ids_eq_union_eq_replay = Q.prove(
  `x ≤ y ∧ y ≤ z ∧ s = probe_set_ids y z ⇒ probe_set_ids x z = probe_set_ids x y ∪ s`,
  fs [set_ids_eq_union_replay]);
val _ = show "set_ids_eq_union_eq_replay_typed" set_ids_eq_union_eq_replay;

val _ = print "env_rel_lift_statement_typed=";
val _ = print_term (Parse.Term `!tenv ienv mn. probe_env_rel tenv ienv ⇒
  probe_env_rel (tenvLift mn tenv) (lift_ienv mn ienv)`);
val _ = print "\n";

val type_config_ok_replay = Q.prove(
  `probe_env_rel prim_tenv init_config ∧ inf_set_tids_ienv prim_type_ids init_config`,
  rw [probe_env_rel_def, inf_set_tids_ienv_def, ienv_ok_def, ienv_val_ok_def,
      typeSoundInvariantsTheory.tenv_ok_def, typeSoundInvariantsTheory.tenv_ctor_ok_def,
      typeSoundInvariantsTheory.tenv_abbrev_ok_def,
      probe_env_rel_sound_def, probe_env_rel_complete_def, init_config_def,
      primTypesTheory.prim_tenv_def, typeSystemTheory.lookup_var_def] >>
  TRY (Cases_on `x`) >> rw [namespaceTheory.nsLookupMod_def] >>
  simp [primTypesTheory.prim_type_ids_def, inf_set_tids_subset_def] >>
  rpt (irule namespacePropsTheory.nsAll_nsBind >>
       rw [unconvert_t_def, inf_set_tids_def, typeSystemTheory.check_freevars_def]) >>
  rw [typeSystemTheory.prim_type_nums_def, lookup_varE_def, tveLookup_def]);
val _ = show "type_config_ok_replay_typed" type_config_ok_replay;

val lookup_varE_empty_replay = Q.prove(
  `!x. lookup_varE x Empty = NONE`,
  rw [lookup_varE_def, tveLookup_def] \\ every_case_tac);
val _ = show "lookup_varE_empty_replay_typed" lookup_varE_empty_replay;

val init_config_tenv_to_ienv_replay = Q.prove(
  `init_config = probe_tenv_to_ienv prim_tenv`,
  rw [init_config_def, probe_tenv_to_ienv_def] \\ EVAL_TAC);
val _ = show "init_config_tenv_to_ienv_replay_typed" init_config_tenv_to_ienv_replay;

(* Replay the original type-soundness local-environment definitions; the
   source theory is not required to be built in the oracle checkout. *)
val probe_tenv_val_exp_ok_def = Define `
  (probe_tenv_val_exp_ok Empty <=> T) /\
  (probe_tenv_val_exp_ok (Bind_tvar n tenv) <=> probe_tenv_val_exp_ok tenv) /\
  (probe_tenv_val_exp_ok (Bind_name x tvs t tenv) <=>
    check_freevars (tvs + num_tvs tenv) [] t /\ probe_tenv_val_exp_ok tenv)`;
val _ = show "tenv_val_exp_ok_replay_typed" probe_tenv_val_exp_ok_def;
val probe_add_tenvE_def = Define `
  (probe_add_tenvE Empty tenvV = tenvV) /\
  (probe_add_tenvE (Bind_tvar n tenvE) tenvV = probe_add_tenvE tenvE tenvV) /\
  (probe_add_tenvE (Bind_name x tvs t tenvE) tenvV =
    nsBind x (tvs,t) (probe_add_tenvE tenvE tenvV))`;
val _ = show "add_tenvE_replay_typed" probe_add_tenvE_def;

val probe_type_ctor_def = Define `
  probe_type_ctor ctMap name (n, stamp) (tvs, ts, ti) <=>
    FLOOKUP ctMap stamp = SOME (tvs, ts, ti) /\ LENGTH ts = n`;
val _ = show "type_ctor_replay_typed" probe_type_ctor_def;

val probe_ctMap_ok_def = Define `
  probe_ctMap_ok ctMap <=>
    FEVERY (\(stamp,(tvs,ts,ti)). EVERY (check_freevars 0 tvs) ts) ctMap /\
    (!ex tvs ts ti. FLOOKUP ctMap (ExnStamp ex) = SOME (tvs,ts,ti) ==>
      tvs = [] /\ ti = Texn_num) /\
    (!cn x tvs ts ti. FLOOKUP ctMap (TypeStamp cn x) = SOME (tvs,ts,ti) ==>
      ~MEM ti prim_type_nums) /\
    (!stamp1 tvs1 ts1 ti stamp2 tvs2 ts2.
      FLOOKUP ctMap stamp1 = SOME (tvs1,ts1,ti) /\
      FLOOKUP ctMap stamp2 = SOME (tvs2,ts2,ti) ==> same_type stamp1 stamp2)`;
val _ = show "ctMap_ok_replay_typed" probe_ctMap_ok_def;
val probe_ctMap_has_exns_def = Define `
  probe_ctMap_has_exns ctMap <=>
    FLOOKUP ctMap bind_stamp = SOME ([],[],Texn_num) /\
    FLOOKUP ctMap chr_stamp = SOME ([],[],Texn_num) /\
    FLOOKUP ctMap div_stamp = SOME ([],[],Texn_num) /\
    FLOOKUP ctMap subscript_stamp = SOME ([],[],Texn_num)`;
val _ = show "ctMap_has_exns_replay_typed" probe_ctMap_has_exns_def;
val probe_ctMap_has_lists_def = Define `
  probe_ctMap_has_lists ctMap <=>
    FLOOKUP ctMap (TypeStamp «[]» list_type_num) = SOME ([«'a»],[],Tlist_num) /\
    FLOOKUP ctMap (TypeStamp «::» list_type_num) =
      SOME ([«'a»],[Tvar «'a»; Tlist (Tvar «'a»)],Tlist_num) /\
    (!cn. cn <> «::» /\ cn <> «[]» ==> FLOOKUP ctMap (TypeStamp cn list_type_num) = NONE)`;
val _ = show "ctMap_has_lists_replay_typed" probe_ctMap_has_lists_def;
val probe_ctMap_has_bools_def = Define `
  probe_ctMap_has_bools ctMap <=>
    FLOOKUP ctMap (TypeStamp «True» bool_type_num) = SOME ([],[],Tbool_num) /\
    FLOOKUP ctMap (TypeStamp «False» bool_type_num) = SOME ([],[],Tbool_num) /\
    (!cn. cn <> «True» /\ cn <> «False» ==> FLOOKUP ctMap (TypeStamp cn bool_type_num) = NONE)`;
val _ = show "ctMap_has_bools_replay_typed" probe_ctMap_has_bools_def;
val probe_good_ctMap_def = Define `
  probe_good_ctMap ctMap <=> probe_ctMap_ok ctMap /\ probe_ctMap_has_bools ctMap /\
    probe_ctMap_has_exns ctMap /\ probe_ctMap_has_lists ctMap`;
val _ = show "good_ctMap_replay_typed" probe_good_ctMap_def;
val probe_consistent_ctMap_def = Define `
  probe_consistent_ctMap (st:'ffi semanticPrimitives$state) type_ids ctMap <=>
    DISJOINT type_ids (FRANGE ((SND o SND) o_f ctMap)) /\
    !cn id.
      (TypeStamp cn id IN FDOM ctMap ==> id < st.next_type_stamp) /\
      (ExnStamp id IN FDOM ctMap ==> id < st.next_exn_stamp)`;
val _ = show "consistent_ctMap_replay_typed" probe_consistent_ctMap_def;
val _ = (print "store_t_replay_typed="; print_thm (TypeBase.axiom_of ``:probe_store_t``); print "\n");
val _ = show "type_v_rules_typed" typeSoundInvariantsTheory.type_v_rules;
val _ = show "type_sv_def_typed" typeSoundInvariantsTheory.type_sv_def;
val _ = show "type_s_def_typed" typeSoundInvariantsTheory.type_s_def;
val _ = show "type_all_env_def_typed" typeSoundInvariantsTheory.type_all_env_def;
val _ = show "type_sound_invariant_def_typed" typeSoundInvariantsTheory.type_sound_invariant_def;
val _ = show "set_tids_subset_typed" inferPropsTheory.set_tids_subset_def;
val _ = show "start_type_id_typed" inferTheory.start_type_id_def;
val probe_set_tids_tenv_def = Define `
  probe_set_tids_tenv tids tenv <=>
    nsAll (\i (ls,t). set_tids_subset tids t) tenv.t /\
    nsAll (\i (ls,ts,tid). EVERY (\t. set_tids_subset tids t) ts /\ tid IN tids) tenv.c /\
    nsAll (\i (n,t). set_tids_subset tids t) tenv.v`;
val _ = show "set_tids_tenv_replay_typed" probe_set_tids_tenv_def;
val set_tids_subset_mono_replay = Q.prove(
  `!tids t tids'. set_tids_subset tids t /\ tids SUBSET tids' ==>
     set_tids_subset tids' t`,
  rw[set_tids_subset_def, SUBSET_DEF]);
val _ = show "set_tids_subset_mono_replay_typed" set_tids_subset_mono_replay;
val set_tids_tenv_mono_replay = Q.prove(
  `probe_set_tids_tenv tids tenv /\ tids SUBSET tids' ==>
     probe_set_tids_tenv tids' tenv`,
  fs[probe_set_tids_tenv_def] >> rw[] >>
  irule namespacePropsTheory.nsAll_mono >>
  goal_assum(first_assum o mp_then Any mp_tac) >>
  rw[] >> pairarg_tac >> fs[EVERY_MEM,SUBSET_DEF] >>
  metis_tac[set_tids_subset_mono_replay,SUBSET_DEF]);
val _ = show "set_tids_tenv_mono_replay_typed" set_tids_tenv_mono_replay;
