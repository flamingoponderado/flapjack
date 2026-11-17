(* Replay environment-conversion declarations and initialization facts from
   envRelScript.sml and repl_typesScript.sml without building those theories. *)
load "inferPropsTheory";
load "namespacePropsTheory";
load "primTypesTheory";
load "typeSysPropsTheory";
load "semanticPrimitivesTheory";
val _ = loadPath := "proofs" :: !loadPath;
load "type_dCanonTheory";
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
val _ = show "bind_guard_typed" inferTheory.bind_guard;
val _ = show "ignore_bind_guard_typed" inferTheory.ignore_bind_guard;
val _ = show "st_ex_bind_pair_typed" inferTheory.st_ex_bind_pair;
val _ = show "st_ex_bind_triple_typed" inferTheory.st_ex_bind_triple;
val _ = show "infer_read_typed" inferTheory.read_def;
val _ = show "infer_write_typed" inferTheory.write_def;
val _ = show "lookup_st_ex_typed" inferTheory.lookup_st_ex_def;
val _ = show "find_dup_typed" inferTheory.find_dup_def;
val _ = show "check_dups_typed" inferTheory.check_dups_def;
val _ = show "check_dups_eq_find_dup_typed" inferTheory.check_dups_eq_find_dup;
val _ = show "type_name_check_subst_typed" inferTheory.type_name_check_subst_def;
val _ = show "type_name_check_sub_typed" inferTheory.type_name_check_sub_def;
val _ = show "to_type_name_check_sub_typed" inferTheory.to_type_name_check_sub;
val _ = show "bind_type_name_check_subst_typed" inferTheory.bind_type_name_check_subst;
val _ = show "ignore_bind_type_name_check_subst_typed" inferTheory.ignore_bind_type_name_check_subst;
val _ = show "type_name_check_sub_unbound_eval" (EVAL ``
  type_name_check_sub <|loc := NONE; err := nsEmpty|> nsEmpty [] (Atvar «a») (7:num)``);
val _ = show "type_name_check_sub_missing_eval" (EVAL ``
  type_name_check_sub <|loc := NONE; err := nsEmpty|> nsEmpty []
    (Atapp [] (Short «missing»)) (7:num)``);
val _ = show "type_name_check_sub_success_eval" (EVAL ``
  type_name_check_sub <|loc := NONE; err := nsEmpty|> nsEmpty [«a»]
    (Attup [Atvar «a»; Atvar «a»]) (7:num)``);
val _ = show "check_ctor_types_typed" inferTheory.check_ctor_types_def;
val _ = show "check_ctors_typed" inferTheory.check_ctors_def;
val _ = show "check_type_definition_typed" inferTheory.check_type_definition_def;
val _ = show "check_ctor_types_expand_typed" inferTheory.check_ctor_types_expand;
val _ = show "check_ctors_expand_typed" inferTheory.check_ctors_expand;
val _ = show "check_type_definition_expand_typed" inferTheory.check_type_definition_expand;
val _ = show "check_type_definition_dup_ctor_eval" (EVAL ``
  check_type_definition <|loc := NONE; err := nsEmpty|> nsEmpty
    [([«a»; «a»], «t», [(«C», []); («C», [])])] (7:num)``);
val _ = show "check_type_definition_dup_type_eval" (EVAL ``
  check_type_definition <|loc := NONE; err := nsEmpty|> nsEmpty
    [([], «t», []); ([], «t», [])] (7:num)``);
val _ = show "check_type_definition_unbound_eval" (EVAL ``
  check_type_definition <|loc := NONE; err := nsEmpty|> nsEmpty
    [([], «t», [(«C», [Atvar «a»])])] (7:num)``);
val _ = show "type_name_check_unbound_eval" (EVAL ``
  type_name_check_subst <|loc := NONE; err := nsEmpty|> (\x. x) nsEmpty [] (Atvar «a») (7:num)``);
val _ = show "type_name_check_tuple_eval" (EVAL ``
  type_name_check_subst <|loc := NONE; err := nsEmpty|> (\x. x) nsEmpty [«a»]
    (Attup [Atvar «a»; Atvar «a»]) (7:num)``);
val _ = show "type_name_check_unknown_ctor_eval" (EVAL ``
  type_name_check_subst <|loc := NONE; err := nsEmpty|> (\x. x) nsEmpty []
    (Atapp [] (Short «missing»)) (7:num)``);
val _ = show "type_name_check_duplicate_param_eval" (EVAL ``
  type_name_check_subst <|loc := NONE; err := nsEmpty|> (\x. x)
    (nsBind «pair» ([«x»; «x»], Tvar «x») nsEmpty) [«a»; «b»]
    (Atapp [Atvar «a»; Atvar «b»] (Short «pair»)) (7:num)``);
val _ = show "type_name_check_arity_eval" (EVAL ``
  type_name_check_subst <|loc := NONE; err := nsEmpty|> (\x. x)
    (nsBind «pair» ([«x»; «y»], Tvar «x») nsEmpty) []
    (Atapp [] (Short «pair»)) (7:num)``);
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
val _ = show "nsMap_I_typed" namespacePropsTheory.nsMap_I;
val _ = show "nsMap_compose_typed" namespacePropsTheory.nsMap_compose;
val _ = show "nsMap_nsAppend_typed" namespacePropsTheory.nsMap_nsAppend;
val _ = show "nsAll_nsLift_typed" namespacePropsTheory.nsAll_nsLift;
val _ = show "nsAll2_nsLift_typed" namespacePropsTheory.nsAll2_nsLift;
val _ = show "ienv_ok_lift_typed" inferPropsTheory.ienv_ok_lift;
val _ = show "ienv_ok_extend_dec_ienv_typed" inferPropsTheory.ienv_ok_extend_dec_ienv;
val _ = show "infer_type_subst_empty_check_typed" inferPropsTheory.infer_type_subst_empty_check;
val _ = show "check_freevars_more_typed" inferPropsTheory.check_freevars_more;
val _ = show "check_t_infer_type_subst_dbs_typed" inferPropsTheory.check_t_infer_type_subst_dbs;
val _ = show "extend_dec_tenv_ok_typed" typeSysPropsTheory.extend_dec_tenv_ok;
val _ = show "tenv_abbrev_ok_lookup_typed" typeSysPropsTheory.tenv_abbrev_ok_lookup;
val _ = show "check_freevars_add_typed" typeSysPropsTheory.check_freevars_add;
val _ = show "check_freevars_subst_single_typed" typeSysPropsTheory.check_freevars_subst_single;
val _ = show "check_freevars_type_name_subst_typed" typeSysPropsTheory.check_freevars_type_name_subst;
val _ = show "type_p_freevars_typed" typeSysPropsTheory.type_p_freevars;
val _ = show "tenv_val_exp_ok_bvl_funs_typed" typeSysPropsTheory.tenv_val_exp_ok_bvl_funs;
val _ = show "num_tvs_bind_var_list_typed" typeSysPropsTheory.num_tvs_bind_var_list;
val _ = show "tenv_val_exp_ok_bvl_typed" typeSysPropsTheory.tenv_val_exp_ok_bvl;
val _ = show "deBruijn_subst_check_freevars_typed" typeSysPropsTheory.deBruijn_subst_check_freevars;
val _ = show "deBruijn_subst_check_freevars2_typed" typeSysPropsTheory.deBruijn_subst_check_freevars2;
val _ = show "check_freevars_subst_inc_typed" typeSysPropsTheory.check_freevars_subst_inc;
val _ = show "tveLookup_freevars_subst_typed" typeSysPropsTheory.tveLookup_freevars_subst;
val _ = show "type_e_freevars_typed" typeSysPropsTheory.type_e_freevars;
val _ = show "check_ctor_tenv_ok_typed" typeSysPropsTheory.check_ctor_tenv_ok;
val _ = show "type_d_canon_tenv_ok_typed" type_dCanonTheory.type_d_canon_tenv_ok;

(* Replay the source proof because inferCompleteTheory is not built here. *)
val inf_set_tids_extend_dec_ienv_replay = Q.prove(
  `inf_set_tids_ienv (count n) ienv2 /\
   inf_set_tids_ienv (count m) ienv /\ m <= n ==>
   inf_set_tids_ienv (count n) (extend_dec_ienv ienv2 ienv)`,
  fs [inf_set_tids_ienv_def] >> rpt disch_tac >> fs [extend_dec_ienv_def] >>
  conj_tac >-
    (match_mp_tac namespacePropsTheory.nsAll_nsAppend >> fs [] >>
     fs [inf_set_tids_unconvert, inf_set_tids_subset_def] >>
     irule namespacePropsTheory.nsAll_mono >>
     goal_assum (first_assum o mp_then Any mp_tac) >>
     rw [SUBSET_DEF, UNCURRY] >> res_tac >> rw []) >>
  conj_tac >-
    (match_mp_tac namespacePropsTheory.nsAll_nsAppend >> fs [] >>
     irule namespacePropsTheory.nsAll_mono >>
     goal_assum (first_assum o mp_then Any mp_tac) >>
     rw [SUBSET_DEF, UNCURRY, inf_set_tids_subset_def] >>
     fs [EVERY_MEM] >> rw [] >> res_tac >> fs []) >>
  match_mp_tac namespacePropsTheory.nsAll_nsAppend >> fs [] >>
  irule namespacePropsTheory.nsAll_mono >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  rw [SUBSET_DEF, UNCURRY, inf_set_tids_subset_def] >> rw [] >> res_tac >> fs []);
val _ = show "inf_set_tids_extend_dec_ienv_replay_typed" inf_set_tids_extend_dec_ienv_replay;

val type_p_pat_bindings_replay = Q.prove(
  `(!tvs tenv p t new_bindings.
      type_p tvs tenv p t new_bindings ==> MAP FST new_bindings = pat_bindings p) /\
   (!tvs tenv ps ts new_bindings.
      type_ps tvs tenv ps ts new_bindings ==> MAP FST new_bindings = pats_bindings ps)`,
  ho_match_mp_tac type_p_ind >> rw [astTheory.pat_bindings_def]);
val _ = show "type_p_pat_bindings_replay_typed" type_p_pat_bindings_replay;

val t_vars_check_t_replay = Q.prove(
  `(!t. ~check_t 0 {} t /\ check_t 0 s t ==>
         ?n'. n' IN s /\ n' IN t_vars t) /\
   (!ts. !x. MEM x ts ==> ~check_t 0 {} x /\ check_t 0 s x ==>
         ?n'. n' IN s /\ n' IN t_vars x)`,
  ho_match_mp_tac infer_tTheory.infer_t_induction >>
  rw [check_t_def, unifyTheory.t_vars_eqn] >>
  fs [EXISTS_MEM, EVERY_MEM] >> res_tac >> qexists_tac `n'` >>
  fs [MEM_MAP] >> metis_tac []);
val _ = show "t_vars_check_t_replay_typed" t_vars_check_t_replay;

val t_walkstar_diff_replay = Q.prove(
  `t_wfs s1 /\ t_wfs s2 /\
    t_walkstar s1 (Infer_Tuvar n) <> t_walkstar s2 (Infer_Tuvar n) ==>
   (!t. n IN t_vars t ==> t_walkstar s1 t <> t_walkstar s2 t) /\
   (!ts. !x. MEM x ts ==> n IN t_vars x ==> t_walkstar s1 x <> t_walkstar s2 x)`,
  strip_tac >> ho_match_mp_tac infer_tTheory.infer_t_induction >>
  rw [unifyTheory.t_vars_eqn] >> fs [] >>
  fs [unifyTheory.t_walkstar_eqn, unifyTheory.t_walk_eqn, MEM_MAP] >>
  res_tac >> rfs [] >> SPOSE_NOT_THEN assume_tac >>
  imp_res_tac MAP_EQ_f >> metis_tac []);
val _ = show "t_walkstar_diff_replay_typed" t_walkstar_diff_replay;

val unconvert_type_subst_replay = Q.prove(
  `(!t subst fvs.
       check_freevars 0 fvs t /\ set fvs SUBSET set (MAP FST subst) ==>
       unconvert_t (type_subst (alist_to_fmap subst) t) =
       infer_type_subst (MAP (\(x,y). (x, unconvert_t y)) subst) t) /\
   (!ts subst fvs.
       EVERY (check_freevars 0 fvs) ts /\ set fvs SUBSET set (MAP FST subst) ==>
       MAP (unconvert_t o type_subst (alist_to_fmap subst)) ts =
       MAP (infer_type_subst (MAP (\(x,y). (x, unconvert_t y)) subst)) ts)`,
  Induct >>
  rw [unconvert_t_def, type_subst_def, infer_type_subst_alt, MAP_MAP_o,
      check_freevars_def] >> fs [combinTheory.o_DEF] >-
    (every_case_tac >> fs [ALOOKUP_MAP] >> fs [] >>
     fs [ALOOKUP_NONE, SUBSET_DEF] >> metis_tac []) >> metis_tac []);
val _ = show "unconvert_type_subst_replay_typed" unconvert_type_subst_replay;

val env_rel_binding_lemma_replay = Q.prove(
  `  !t fvs fvs' subst.
   check_freevars 0 fvs' t ∧
   set fvs' ⊆ set fvs ∧
   ALL_DISTINCT fvs'
   ⇒
   infer_deBruijn_subst subst
     (infer_type_subst (ZIP (fvs',MAP Infer_Tvar_db (COUNT_LIST (LENGTH (fvs'))))) t) =
   infer_deBruijn_subst
     (GENLIST (λn.
          infer_deBruijn_subst subst
            (case find_index (EL n fvs) fvs' 0 of
               NONE => Infer_Tapp [] arb
             | SOME t => Infer_Tvar_db t)) (LENGTH fvs))
     (infer_type_subst (ZIP (fvs,GENLIST (λx. Infer_Tvar_db x) (LENGTH fvs))) t)`,
  ho_match_mp_tac t_ind >>
  rw [infer_type_subst_alt, infer_deBruijn_subst_alt, check_freevars_def]
  >- (
    qmatch_assum_abbrev_tac `MEM name _` >>
    every_case_tac >>
    fs [ALOOKUP_FAILS, SUBSET_DEF, MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST,
        infer_deBruijn_subst_alt]
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_alt, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_alt, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_alt, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      imp_res_tac ALOOKUP_MEM >>
      fs [MEM_ZIP, LENGTH_COUNT_LIST] >>
      rw [] >>
      fs [EL_MAP, LENGTH_COUNT_LIST, infer_deBruijn_subst_alt, EL_COUNT_LIST] >>
      drule find_index_ALL_DISTINCT_EL >>
      disch_then drule >>
      disch_then (qspec_then `0` mp_tac) >>
      asm_simp_tac std_ss [] >>
      rw [infer_deBruijn_subst_alt]))
  >- (
    irule LIST_EQ >>
    rw [EL_MAP] >>
    fs [EVERY_EL]));
val _ = show "env_rel_binding_lemma_replay_typed" env_rel_binding_lemma_replay;
val _ = if List.exists (fn v => fst (dest_var v) = "arb")
              (free_vars (concl env_rel_binding_lemma_replay)) then ()
        else raise Fail "expected source arb to remain a free variable";

val env_rel_binding_lemma2_replay = Q.prove(
  `   !t fvs fvs' subst.
    check_freevars 0 fvs' t ∧
    set fvs' ⊆ set fvs ∧
    ALL_DISTINCT fvs'
    ⇒
    infer_deBruijn_subst subst
      (infer_type_subst (ZIP (fvs,GENLIST (λx. Infer_Tvar_db x) (LENGTH fvs))) t) =
    infer_deBruijn_subst
      (GENLIST (λn.
           infer_deBruijn_subst subst
             (case find_index (EL n fvs') fvs 0 of
                NONE => Infer_Tapp [] TC_int
              | SOME t => Infer_Tvar_db t)) (LENGTH fvs'))
      (infer_type_subst (ZIP (fvs',MAP Infer_Tvar_db (COUNT_LIST (LENGTH fvs')))) t)`,
  ho_match_mp_tac t_ind >>
  rw [infer_type_subst_alt, infer_deBruijn_subst_alt, check_freevars_def]
  >- (
    qmatch_assum_abbrev_tac `MEM name _` >>
    every_case_tac >>
    fs [ALOOKUP_FAILS, SUBSET_DEF, MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST,
        infer_deBruijn_subst_alt]
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_alt, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_alt, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_alt, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      imp_res_tac ALOOKUP_MEM >>
      fs [MEM_ZIP, LENGTH_COUNT_LIST] >>
      rw [] >>
      fs [EL_MAP, LENGTH_COUNT_LIST, infer_deBruijn_subst_alt, EL_COUNT_LIST] >>
      imp_res_tac ALOOKUP_find_index_SOME >>
      fs [MAP_ZIP, EL_ZIP, LENGTH_GENLIST, LENGTH_ZIP] >>
      rfs [MAP_ZIP, EL_ZIP, LENGTH_GENLIST, LENGTH_ZIP] >>
      rw [infer_deBruijn_subst_alt]))
  >- (
    irule LIST_EQ >>
    rw [EL_MAP] >>
    fs [EVERY_EL]));
val _ = show "env_rel_binding_lemma2_replay_typed" env_rel_binding_lemma2_replay;
val _ = if List.exists (fn v => fst (dest_var v) = "TC_int")
              (free_vars (concl env_rel_binding_lemma2_replay)) then ()
        else raise Fail "expected source TC_int to remain a free variable";

val infer_type_subst_check_t_less_replay = Q.prove(
  `  LENGTH ls = LENGTH tvs ∧
  EVERY (check_t n {}) ls ⇒
  (!t.
  check_freevars n tvs t
  ⇒
  check_t n {} (infer_type_subst (ZIP (tvs,ls)) t)) ∧
  (!ts.
  EVERY (check_freevars n tvs) ts
  ⇒
  EVERY (check_t n {}) (MAP (infer_type_subst (ZIP(tvs,ls))) ts))`,
  strip_tac>>
  Induct>>rw[]
  >-
    (rename1 ‘Tvar s’>>
     fs[check_freevars_def,infer_type_subst_alt]>>
    `?x. ALOOKUP (ZIP(tvs,ls)) s = SOME x` by
      (Cases_on `ALOOKUP (ZIP(tvs,ls)) s` >> fs [ALOOKUP_NONE] >> metis_tac [MAP_ZIP])>>
    imp_res_tac ALOOKUP_MEM>>
    Q.ISPECL_THEN [`tvs`,`ls`,`s,x`] assume_tac MEM_ZIP>> rfs[]>>
    metis_tac[EVERY_EL])
  >>
    fs[infer_type_subst_alt,check_t_def,check_freevars_def]>>
    fs[EVERY_MAP]>>metis_tac[]);
val _ = show "infer_type_subst_check_t_less_replay_typed" infer_type_subst_check_t_less_replay;

val check_freevars_deBruijn_inc_replay = Q.prove(
  `!tvs tvs' t. check_freevars tvs tvs' t ==>
    !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t)`,
  ho_match_mp_tac check_freevars_ind >>
  srw_tac[][check_freevars_def, deBruijn_inc_def] >>
  full_simp_tac(srw_ss())[EVERY_MAP, EVERY_MEM] >>
  srw_tac[][check_freevars_def] >> decide_tac);
val _ = show "check_freevars_deBruijn_inc_replay_typed" check_freevars_deBruijn_inc_replay;

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

val convert_bi_remove_replay = Q.prove(
  `probe_convert_t A = probe_convert_t B /\
   check_t n {} A /\ check_t m {} B ==> A = B`,
  rw [] >> last_x_assum (assume_tac o (Q.AP_TERM `unconvert_t`)) >>
  metis_tac [check_t_empty_unconvert_convert_id_replay]);
val _ = show "convert_bi_remove_replay_typed" convert_bi_remove_replay;

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

(* Replay the full source proof over the corresponding reconstructed relation. *)
local
  open typeSysPropsTheory unifyTheory
in
val probe_lookup_varE_empty = Q.prove(
  `!x. lookup_varE x Empty = NONE`,
  rw [lookup_varE_def, tveLookup_def] >> every_case_tac >> fs []);
val env_rel_binding_replay = Q.prove(
  `   !fvs t fvs' name.
   check_freevars 0 fvs' t ∧
   set fvs' ⊆ set fvs
   ⇒
   probe_env_rel
     <|v :=
        nsSing name
          (LENGTH fvs,
           type_subst
             (alist_to_fmap (ZIP (fvs,MAP Tvar_db (GENLIST (λx. x) (LENGTH fvs)))))
             t);
      c := nsEmpty;
      t := nsEmpty|>
    <|inf_v :=
        nsSing name
          (LENGTH (nub fvs'),
           infer_type_subst
             (ZIP (nub fvs', MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub fvs')))))
             t);
      inf_c := nsEmpty;
      inf_t := nsEmpty|>`,
  rw [probe_env_rel_def]
  >- (
    rw [ienv_ok_def, ienv_val_ok_def] >>
    Cases_on `nub fvs' = []` >>
    fs []
    >- (
      simp [COUNT_LIST_def, nub_def] >>
      irule (CONJUNCT1 infer_type_subst_empty_check) >> simp[])
    >- (
      irule check_t_infer_type_subst_dbs >>
      qexists_tac `0` >>
      rw [] >>
      metis_tac [check_freevars_type_name_subst]))
  >- (
    rw [typeSoundInvariantsTheory.tenv_ok_def, typeSoundInvariantsTheory.tenv_val_ok_def] >>
    irule check_freevars_subst_single >>
    rw [EVERY_MAP, EVERY_GENLIST, check_freevars_def] >>
    rw [] >>
    irule check_freevars_add >>
    qexists_tac `0` >>
    rw [] >>
    irule check_freevars_more >>
    metis_tac [])
  >- (
    rw [probe_env_rel_sound_def, lookup_var_def, probe_lookup_varE_empty]
    >- (
      irule check_freevars_subst_single >>
      rw [EVERY_MAP, EVERY_GENLIST, check_freevars_def] >>
      irule check_freevars_add >>
      qexists_tac `0` >>
      rw [] >>
      irule check_freevars_more >>
      metis_tac []) >>
    rw [probe_tscheme_approx_def, t_walkstar_FEMPTY] >>
    drule (CONJUNCT1 unconvert_type_subst_replay) >>
    disch_then (qspec_then `ZIP (fvs,MAP Tvar_db (GENLIST (λx. x) (LENGTH fvs)))` mp_tac) >>
    impl_tac
    >- (
      fs [SUBSET_DEF] >>
      rw [MEM_MAP, MEM_ZIP, LENGTH_GENLIST] >>
      fs [PULL_EXISTS] >>
      metis_tac [MEM_EL]) >>
    simp [] >>
    disch_then kall_tac >>
    `MAP (\(x,y). (x:mlstring, unconvert_t y)) = MAP (\p. (FST p, unconvert_t (SND p)))`
      by (AP_TERM_TAC >> rw [LAMBDA_PROD]) >>
    simp [GSYM ZIP_MAP, LENGTH_GENLIST, MAP_GENLIST, combinTheory.o_DEF, unconvert_t_def] >>
    EXISTS_TAC ``GENLIST (\n. case find_index (EL n (fvs:tvarN list)) (nub fvs') 0
                                of NONE => Infer_Tapp [] TC_int
                                 | SOME t => Infer_Tvar_db t) (LENGTH fvs)`` >>
    rw [EVERY_GENLIST]
    >- (
      every_case_tac >>
      rw [check_t_def] >>
      drule find_index_LESS_LENGTH >>
      rw []) >>
    rw [MAP_GENLIST, combinTheory.o_DEF] >>
    irule env_rel_binding_lemma_replay >>
    rw [all_distinct_nub] >>
    metis_tac [check_freevars_more, nub_set, SUBSET_DEF])
  >- (
   rw [probe_env_rel_complete_def, lookup_var_def, probe_lookup_varE_empty]
   >- (
     qexists_tac `LENGTH fvs` >>
     irule check_freevars_subst_single >>
     rw [EVERY_MAP, EVERY_GENLIST, check_freevars_def] >>
     irule check_freevars_add >>
     qexists_tac `0` >>
     rw [] >>
     irule check_freevars_more >>
     metis_tac []) >>
    rw [probe_tscheme_approx_def, t_walkstar_FEMPTY] >>
    drule (CONJUNCT1 unconvert_type_subst_replay) >>
    disch_then (qspec_then `ZIP (fvs,MAP Tvar_db (GENLIST (λx. x) (LENGTH fvs)))` mp_tac) >>
    impl_tac
    >- (
      fs [SUBSET_DEF] >>
      rw [MEM_MAP, MEM_ZIP, LENGTH_GENLIST] >>
      fs [PULL_EXISTS] >>
      metis_tac [MEM_EL]) >>
    simp [] >>
    disch_then kall_tac >>
    `MAP (\(x,y). (x:mlstring, unconvert_t y)) = MAP (\p. (FST p, unconvert_t (SND p)))`
      by (AP_TERM_TAC >> rw [LAMBDA_PROD]) >>
    simp [GSYM ZIP_MAP, LENGTH_GENLIST, MAP_GENLIST, combinTheory.o_DEF, unconvert_t_def] >>
    EXISTS_TAC ``GENLIST (\n. case find_index (EL n (nub fvs':tvarN list)) fvs 0
                                of NONE => Infer_Tapp [] TC_int
                                 | SOME t => Infer_Tvar_db t) (LENGTH (nub fvs'))`` >>
    rw [EVERY_GENLIST]
    >- (
      every_case_tac >>
      rw [check_t_def] >>
      drule find_index_LESS_LENGTH >>
      rw []) >>
    rw [MAP_GENLIST, combinTheory.o_DEF] >>
    irule env_rel_binding_lemma2_replay >>
    rw [all_distinct_nub] >>
    metis_tac [check_freevars_more, nub_set, SUBSET_DEF]));
end;
val _ = show "env_rel_binding_replay_typed" env_rel_binding_replay;

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
val _ = show "set_tids_subset_type_subst_typed" inferPropsTheory.set_tids_subset_type_subst;
val _ = show "set_tids_subset_type_name_subst_typed" inferPropsTheory.set_tids_subset_type_name_subst;
val _ = show "prim_tids_typed" inferPropsTheory.prim_tids_def;
val _ = show "start_type_id_prim_tids_count_typed" inferPropsTheory.start_type_id_prim_tids_count;
val _ = show "ts_tid_rename_typed" inferPropsTheory.ts_tid_rename_def;
val _ = show "ts_tid_rename_I_typed" inferPropsTheory.ts_tid_rename_I;
val _ = show "set_tids_ts_tid_rename_typed" inferPropsTheory.set_tids_ts_tid_rename;
val _ = show "remap_tenv_typed" inferPropsTheory.remap_tenv_def;
val _ = show "remap_tenv_I_typed" inferPropsTheory.remap_tenv_I;
val _ = show "start_type_id_typed" inferTheory.start_type_id_def;
val probe_set_tids_tenv_def = Define `
  probe_set_tids_tenv tids tenv <=>
    nsAll (\i (ls,t). set_tids_subset tids t) tenv.t /\
    nsAll (\i (ls,ts,tid). EVERY (\t. set_tids_subset tids t) ts /\ tid IN tids) tenv.c /\
    nsAll (\i (n,t). set_tids_subset tids t) tenv.v`;
val _ = show "set_tids_tenv_replay_typed" probe_set_tids_tenv_def;
val _ = show "tenv_equiv_typed" type_dCanonTheory.tenv_equiv_def;
val _ = show "tenv_equiv_refl_typed" type_dCanonTheory.tenv_equiv_refl;
val _ = show "tenv_equiv_sym_typed" type_dCanonTheory.tenv_equiv_sym;
val _ = show "tenv_equiv_tenvLift_typed" type_dCanonTheory.tenv_equiv_tenvLift;
val _ = show "lookup_var_tenv_equiv_typed" type_dCanonTheory.lookup_var_tenv_equiv;
val _ = show "check_type_names_tenv_equiv_typed" type_dCanonTheory.check_type_names_tenv_equiv;
val _ = show "type_name_subst_tenv_equiv_typed" type_dCanonTheory.type_name_subst_tenv_equiv;
val _ = show "type_p_tenv_equiv_typed" type_dCanonTheory.type_p_tenv_equiv;
val _ = show "type_p_ts_tid_rename_typed" type_dCanonTheory.type_p_ts_tid_rename;
val _ = show "type_op_ts_tid_rename_typed" type_dCanonTheory.type_op_ts_tid_rename;
val _ = show "type_e_ts_tid_rename_typed" type_dCanonTheory.type_e_ts_tid_rename;
val _ = show "type_funs_ts_tid_rename_sing_renum_typed" type_dCanonTheory.type_funs_ts_tid_rename_sing_renum;
val type_p_ts_tid_rename_sing_renum_replay = Q.prove(
  `m NOTIN tids /\ prim_tids T tids /\ type_p tvs tenv p t bindings /\
   type_dCanon$set_tids_tenv tids tenv ==>
   type_p tvs tenv p (ts_tid_rename (type_dCanon$sing_renum m n) t)
     (MAP (\(nn,t). (nn,ts_tid_rename (type_dCanon$sing_renum m n) t)) bindings)`,
  rw[] >>
  `type_dCanon$good_remap (type_dCanon$sing_renum m n)` by
    (fs[type_dCanonTheory.good_remap_def,type_dCanonTheory.sing_renum_def] >>
     fs[prim_tids_def] >> rw[] >> fs[] >> simp[MAP_EQ_ID] >>
     fs[prim_type_nums_def] >> rw[] >> fs[]) >>
  drule type_dCanonTheory.type_p_ts_tid_rename >>
  strip_tac >> first_x_assum drule >>
  drule type_dCanonTheory.sing_renum_NOTIN_tenv_ID >>
  simp[] >> rw[] >> metis_tac[type_dCanonTheory.type_p_tenv_equiv]);
val _ = show "type_p_ts_tid_rename_sing_renum_replay_typed" type_p_ts_tid_rename_sing_renum_replay;
val type_e_ts_tid_rename_sing_renum_replay = Q.prove(
  `m NOTIN tids /\ prim_tids T tids /\ type_e tenv tenvE e t /\
   type_dCanon$set_tids_tenv tids tenv ==>
   type_e tenv (type_dCanon$remap_tenvE (type_dCanon$sing_renum m n) tenvE) e
     (ts_tid_rename (type_dCanon$sing_renum m n) t)`,
  rw[] >>
  `type_dCanon$good_remap (type_dCanon$sing_renum m n)` by
    (fs[type_dCanonTheory.good_remap_def,type_dCanonTheory.sing_renum_def] >>
     fs[prim_tids_def] >> rw[] >> fs[] >> simp[MAP_EQ_ID] >>
     fs[prim_type_nums_def] >> rw[] >> fs[]) >>
  drule type_dCanonTheory.type_e_ts_tid_rename >>
  strip_tac >> first_x_assum drule >>
  drule type_dCanonTheory.sing_renum_NOTIN_tenv_ID >>
  simp[] >> rw[] >> metis_tac[type_dCanonTheory.type_e_tenv_equiv]);
val _ = show "type_e_ts_tid_rename_sing_renum_replay_typed" type_e_ts_tid_rename_sing_renum_replay;
val _ = show "linv_def_typed" pred_setTheory.LINV_DEF;
val _ = show "good_remap_LINV_typed" type_dCanonTheory.good_remap_LINV;
val _ = show "ts_tid_rename_LINV_typed" type_dCanonTheory.ts_tid_rename_LINV;
val _ = show "inj_linv_opt_typed" pred_setTheory.INJ_LINV_OPT;
val _ = show "linvi_def_typed" type_dCanonTheory.LINVI_def;
val _ = show "inj_LINVI_typed" type_dCanonTheory.INJ_LINVI;
val _ = show "LINVI_RINV_typed" type_dCanonTheory.LINVI_RINV;
val _ = show "good_remap_LINVI_typed" type_dCanonTheory.good_remap_LINVI;
val _ = show "ts_tid_rename_LINVI_typed" type_dCanonTheory.ts_tid_rename_LINVI;
val _ = show "remap_tenv_LINV_typed" type_dCanonTheory.remap_tenv_LINV;
val _ = show "good_remap_BIJ_typed" type_dCanonTheory.good_remap_BIJ;
val _ = show "remap_tenv_LINVI_typed" type_dCanonTheory.remap_tenv_LINVI;
val _ = show "ts_tid_rename_compose_typed" type_dCanonTheory.ts_tid_rename_compose;
val _ = show "remap_tenv_compose_typed" type_dCanonTheory.remap_tenv_compose;
val _ = show "ts_tid_rename_eq_id_typed" type_dCanonTheory.ts_tid_rename_eq_id;
val _ = show "ts_tid_rename_eq_f_typed" type_dCanonTheory.ts_tid_rename_eq_f;
val _ = show "inj_ts_tid_rename_eq_typed" type_dCanonTheory.inj_ts_tid_rename_eq;
val _ = show "remap_tenvE_typed" type_dCanonTheory.remap_tenvE_def;
val _ = show "remap_tenvE_bind_tvar_typed" type_dCanonTheory.remap_tenvE_bind_tvar;
val num_tvs_remap_tenvE_replay = Q.prove(
  `!tenvE. num_tvs (remap_tenvE f tenvE) = num_tvs tenvE`,
  Induct >> fs[type_dCanonTheory.remap_tenvE_def]);
val _ = show "num_tvs_remap_tenvE_replay_typed" num_tvs_remap_tenvE_replay;
val remap_tenvE_bind_var_list_replay = Q.prove(
  `!n env tenvE. remap_tenvE f (bind_var_list n env tenvE) =
     bind_var_list n (MAP (\(n,t). (n,ts_tid_rename f t)) env) (remap_tenvE f tenvE)`,
  ho_match_mp_tac bind_var_list_ind >>
  fs[bind_var_list_def,type_dCanonTheory.remap_tenvE_def] >> rw[]);
val _ = show "remap_tenvE_bind_var_list_replay_typed" remap_tenvE_bind_var_list_replay;
val deBruijn_inc_ts_tid_rename_replay = Q.prove(
  `!skip n t. ts_tid_rename f (deBruijn_inc skip n t) =
     deBruijn_inc skip n (ts_tid_rename f t)`,
  ho_match_mp_tac deBruijn_inc_ind >>
  rw[deBruijn_inc_def,ts_tid_rename_def,MAP_MAP_o] >> fs[MAP_EQ_f]);
val _ = show "deBruijn_inc_ts_tid_rename_replay_typed" deBruijn_inc_ts_tid_rename_replay;
val lookup_varE_remap_tenvE_replay = Q.prove(
  `!n tenvE. lookup_varE n (remap_tenvE f tenvE) =
     OPTION_MAP (\(id,t). (id,ts_tid_rename f t)) (lookup_varE n tenvE)`,
  fs[lookup_varE_def] >> Cases >> fs[] >>
  qabbrev_tac `n=0n` >> pop_assum kall_tac >> qid_spec_tac `n` >>
  Induct_on `tenvE` >> fs[type_dCanonTheory.remap_tenvE_def,tveLookup_def] >> rw[] >>
  fs[deBruijn_inc_ts_tid_rename_replay]);
val _ = show "lookup_varE_remap_tenvE_replay_typed" lookup_varE_remap_tenvE_replay;
val ts_tid_rename_deBruijn_subst_replay = Q.prove(
  `!n targs t. ts_tid_rename f (deBruijn_subst n targs t) =
     deBruijn_subst n (MAP (ts_tid_rename f) targs) (ts_tid_rename f t)`,
  ho_match_mp_tac deBruijn_subst_ind >> rw[] >>
  rw[ts_tid_rename_def,deBruijn_subst_def] >>
  fs[EL_MAP,MAP_MAP_o] >> fs[MAP_EQ_f]);
val _ = show "ts_tid_rename_deBruijn_subst_replay_typed" ts_tid_rename_deBruijn_subst_replay;
val _ = show "type_e_tenv_equiv_typed" type_dCanonTheory.type_e_tenv_equiv;
val _ = show "type_pe_determ_tenv_equiv_typed" type_dCanonTheory.type_pe_determ_tenv_equiv;
val _ = show "type_pe_determ_canon_typed" type_dCanonTheory.type_pe_determ_canon_def;
val _ = show "type_pe_determ_canon_tenv_equiv_typed" type_dCanonTheory.type_pe_determ_canon_tenv_equiv;
val _ = show "type_pe_determ_remap_typed" type_dCanonTheory.type_pe_determ_remap;
val _ = show "type_d_type_d_canon_typed" type_dCanonTheory.type_d_type_d_canon;
val _ = show "DISJOINT_CARD_UNION_typed" type_dCanonTheory.DISJOINT_CARD_UNION;
val _ = show "build_ctor_tenv_type_identities_typed" type_dCanonTheory.build_ctor_tenv_type_identities;
val _ = show "nsAll_alist_to_ns_typed" namespacePropsTheory.nsAll_alist_to_ns;
val _ = show "check_ctor_tenv_change_tenvT_typed" typeSysPropsTheory.check_ctor_tenv_change_tenvT;
val _ = show "type_funs_MAP_FST_typed" typeSysPropsTheory.type_funs_MAP_FST;
val _ = show "type_es_length_typed" typeSysPropsTheory.type_es_length;
val _ = show "type_d_canon_rules_typed" type_dCanonTheory.type_d_canon_rules;
val _ = show "good_remap_typed" type_dCanonTheory.good_remap_def;
val _ = show "sing_renum_typed" type_dCanonTheory.sing_renum_def;
val sing_renum_NOT_tscheme_inst_replay = Q.prove(
  `!t. m IN set_tids t /\ m <> n ==>
    ts_tid_rename (type_dCanon$sing_renum m n) t <> t /\
    !tvs tvs'.
      ~tscheme_inst (tvs,ts_tid_rename (type_dCanon$sing_renum m n) t) (tvs',t) /\
      ~tscheme_inst (tvs',t) (tvs,ts_tid_rename (type_dCanon$sing_renum m n) t)`,
  ho_match_mp_tac t_ind >> rw[] >>
  fs[set_tids_def,ts_tid_rename_def,type_dCanonTheory.sing_renum_def] >>
  rw[] >> simp[tscheme_inst_def,deBruijn_subst_def] >> fs[EVERY_MEM,MEM_MAP]
  >- (CCONTR_TAC >> fs[MAP_EQ_ID] >> metis_tac[])
  >- (rw[] >> CCONTR_TAC >> fs[MAP_EQ_f, EVERY_MEM] >>
      last_x_assum mp_tac >> rw[] >> asm_exists_tac >> simp[] >>
      fsrw_tac[DNF_ss][tscheme_inst_def] >> disj2_tac >> disj1_tac >>
      fs[check_freevars_def,EVERY_MEM] >> metis_tac[])
  >> (rw[] >> CCONTR_TAC >> fs[MAP_EQ_f, EVERY_MEM] >>
      last_x_assum mp_tac >> rw[] >> asm_exists_tac >> simp[] >>
      fsrw_tac[DNF_ss][tscheme_inst_def] >> disj2_tac >> disj2_tac >>
      fs[check_freevars_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,MAP_MAP_o,MAP_EQ_ID] >>
      metis_tac[]));
val _ = show "sing_renum_NOT_tscheme_inst_replay_typed" sing_renum_NOT_tscheme_inst_replay;
val type_pe_bindings_tids_replay = Q.prove(
  `prim_tids T tids /\ type_dCanon$set_tids_tenv tids tenv /\
   type_p tvs tenv p t bindings /\ type_e tenv (bind_tvar tvs Empty) e t /\
   (!tvs' bindings' t'. type_p tvs' tenv p t' bindings' /\
       type_e tenv (bind_tvar tvs' Empty) e t' ==>
       LIST_REL tscheme_inst (MAP SND (MAP (\(n,t). (n,tvs',t)) bindings'))
         (MAP SND (MAP (\(n,t). (n,tvs,t)) bindings))) ==>
   !p_1 p_2. MEM (p_1,p_2) bindings ==> set_tids_subset tids p_2`,
  CCONTR_TAC >> fs[set_tids_subset_def,SUBSET_DEF] >>
  drule (GEN_ALL type_p_ts_tid_rename_sing_renum_replay) >>
  rpt (disch_then drule) >> disch_then(qspec_then `x+1` mp_tac) >> strip_tac >>
  first_x_assum drule >>
  drule (GEN_ALL type_e_ts_tid_rename_sing_renum_replay) >>
  rpt (disch_then drule) >> disch_then(qspec_then `x+1` mp_tac) >>
  qmatch_goalsub_abbrev_tac `type_e _ tenvEE _ _` >>
  `tenvEE = (bind_tvar tvs Empty)` by
    rw[Abbr`tenvEE`,bind_tvar_def,type_dCanonTheory.remap_tenvE_def] >>
  pop_assum SUBST_ALL_TAC >> simp[] >> rw[LIST_REL_EL_EQN] >>
  fs[MEM_EL] >> asm_exists_tac >> fs[EL_MAP] >>
  qpat_x_assum `(_,_) = _` sym_sub_tac >> fs[] >>
  `x <> x+1` by fs[] >> metis_tac[sing_renum_NOT_tscheme_inst_replay]);
val _ = show "type_pe_bindings_tids_replay_typed" type_pe_bindings_tids_replay;
val _ = show "type_funs_bindings_tids_typed" type_dCanonTheory.type_funs_bindings_tids;
val _ = show "type_pe_bindings_tids_0_typed" type_dCanonTheory.type_pe_bindings_tids_0;
val _ = show "sing_renum_NOTIN_ID_typed" type_dCanonTheory.sing_renum_NOTIN_ID;
val _ = show "sing_renum_IN_NOT_ID_typed" type_dCanonTheory.sing_renum_IN_NOT_ID;
val _ = show "sing_renum_NOTIN_tenv_ID_typed" type_dCanonTheory.sing_renum_NOTIN_tenv_ID;
val _ = show "extend_bij_typed" type_dCanonTheory.extend_bij_def;
val _ = show "extend_bij_id_typed" type_dCanonTheory.extend_bij_id;
val _ = show "extend_bij_compose_typed" type_dCanonTheory.extend_bij_compose;
val _ = show "BIJ_extend_bij_typed" type_dCanonTheory.BIJ_extend_bij;
val good_remap_extend_bij_replay = Q.prove(
  `type_dCanon$good_remap f /\ prim_tids F ids ==>
     type_dCanon$good_remap (type_dCanon$extend_bij f g ids n)`,
  rw[type_dCanonTheory.good_remap_def, type_dCanonTheory.extend_bij_def,
     prim_tids_def, prim_type_nums_def]);
val _ = show "good_remap_extend_bij_replay_typed" good_remap_extend_bij_replay;
val check_freevars_ts_tid_rename_replay = Q.prove(
  `!ts ls t. check_freevars ts ls (ts_tid_rename f t) <=> check_freevars ts ls t`,
  ho_match_mp_tac check_freevars_ind >>
  fs[ts_tid_rename_def,check_freevars_def,EVERY_MAP,EVERY_MEM]);
val _ = show "check_freevars_ts_tid_rename_replay_typed" check_freevars_ts_tid_rename_replay;
val ts_tid_rename_type_subst_replay = Q.prove(
  `!s t f. ts_tid_rename f (type_subst s t) =
     type_subst (ts_tid_rename f o_f s) (ts_tid_rename f t)`,
  ho_match_mp_tac type_subst_ind >>
  rw[type_subst_def,ts_tid_rename_def] >-
    (TOP_CASE_TAC >> fs[FLOOKUP_o_f,ts_tid_rename_def]) >>
  fs[MAP_MAP_o,MAP_EQ_f]);
val _ = show "ts_tid_rename_type_subst_replay_typed" ts_tid_rename_type_subst_replay;
val check_type_names_ts_tid_rename_replay = Q.prove(
  `!tenvt t. check_type_names tenvt t <=>
     check_type_names (nsMap (\(ls,t). (ls,ts_tid_rename f t)) tenvt) t`,
  ho_match_mp_tac check_type_names_ind >> rw[check_type_names_def] >>
  fs[EVERY_MEM,namespacePropsTheory.nsLookup_nsMap] >>
  Cases_on `nsLookup tenvt tn` >> fs[] >> pairarg_tac >> fs[]);
val _ = show "check_type_names_ts_tid_rename_replay_typed" check_type_names_ts_tid_rename_replay;
val ts_tid_rename_type_name_subst_replay = Q.prove(
  `!tenvt t f tenv. type_dCanon$good_remap f /\ check_type_names tenvt t ==>
     ts_tid_rename f (type_name_subst tenvt t) =
       type_name_subst (nsMap (\(ls,t). (ls,ts_tid_rename f t)) tenvt) t`,
  ho_match_mp_tac type_name_subst_ind >> rw[] >>
  fs[type_name_subst_def,ts_tid_rename_def,check_type_names_def,EVERY_MEM] >-
    (reverse CONJ_TAC >- fs[type_dCanonTheory.good_remap_def,prim_type_nums_def] >>
     fs[MAP_MAP_o,MAP_EQ_f]) >-
    fs[type_dCanonTheory.good_remap_def,prim_type_nums_def] >-
    (simp[namespacePropsTheory.nsLookup_nsMap] >>
     TOP_CASE_TAC >> fs[ts_tid_rename_def] >>
     pairarg_tac >> fs[ts_tid_rename_def] >>
     simp[ts_tid_rename_type_subst_replay] >>
     AP_THM_TAC >> AP_TERM_TAC >>
     fs[GSYM alist_to_fmap_MAP_values] >>
     AP_TERM_TAC >> match_mp_tac LIST_EQ >> fs[EL_MAP,EL_ZIP] >>
     metis_tac[EL_MEM]));
val _ = show "ts_tid_rename_type_name_subst_replay_typed" ts_tid_rename_type_name_subst_replay;
val _ = show "set_tids_tenv_remap_typed" type_dCanonTheory.set_tids_tenv_remap;
val set_tids_tenv_remap_replay = Q.prove(
  `probe_set_tids_tenv tids tenv ==>
     probe_set_tids_tenv (IMAGE f tids) (remap_tenv f tenv)`,
  rw[probe_set_tids_tenv_def, remap_tenv_def, namespacePropsTheory.nsAll_nsMap,
     set_tids_subset_def, UNCURRY, set_tids_ts_tid_rename, EVERY_MAP] >>
  fs[LAMBDA_PROD] >>
  first_assum(mp_then Any match_mp_tac namespacePropsTheory.nsAll_mono) >>
  simp[FORALL_PROD, EVERY_MEM] >> metis_tac[]);
val _ = show "set_tids_tenv_remap_replay_typed" set_tids_tenv_remap_replay;
val remap_tenv_extend_dec_tenv_replay = Q.prove(
  `remap_tenv f (extend_dec_tenv t t') =
     extend_dec_tenv (remap_tenv f t) (remap_tenv f t')`,
  fs[remap_tenv_def, extend_dec_tenv_def, namespacePropsTheory.nsMap_nsAppend]);
val _ = show "remap_tenv_extend_dec_tenv_replay_typed" remap_tenv_extend_dec_tenv_replay;
val set_tids_tenv_extend_dec_tenv_replay = Q.prove(
  `!s t s' t'. probe_set_tids_tenv (s' UNION s) t' /\
     probe_set_tids_tenv (s' UNION s) t ==>
     probe_set_tids_tenv (s' UNION s) (extend_dec_tenv t' t)`,
  rw[extend_dec_tenv_def,probe_set_tids_tenv_def,namespacePropsTheory.nsAll_nsAppend]);
val _ = show "set_tids_tenv_extend_dec_tenv_replay_typed" set_tids_tenv_extend_dec_tenv_replay;
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
