(* Typed first-order term and inference-type encoding declarations. *)
load "unifyTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "term_axiom_typed" termTheory.term_Axiom;
val _ = show "pair_count_def_typed" termTheory.pair_count_def;
val _ = show "vars_def_typed" termTheory.vars_def;
val _ = show "FINITE_vars_typed" termTheory.FINITE_vars;
val _ = show "varb_def_typed" termTheory.varb_def;
val _ = show "FINITE_varb_typed" termTheory.FINITE_varb;
val _ = show "IN_varb_vars_typed" termTheory.IN_varb_vars;
val _ = show "mlt1_def_typed" bagTheory.mlt1_def;
val _ = show "WF_mlt1_typed" bagTheory.WF_mlt1;
val _ = show "FINITE_BAG_UNION_typed" bagTheory.FINITE_BAG_UNION;
val _ = show "mlt1_BAG_INSERT_typed" tcallUnifTheory.mlt1_BAG_INSERT;
val _ = show "mlt_BAG_INSERT2_typed" unifyTheory.mlt_BAG_INSERT2;
val _ = show "vwalk_rangevars_typed" tcallUnifTheory.vwalk_rangevars;
val _ = show "substvars_FUPDATE_typed" tcallUnifTheory.substvars_FUPDATE;
val _ = show "unify_def_typed" unifDefTheory.unify_def;
val _ = show "TC_vR_SUBMAP_typed" unifPropsTheory.TC_vR_SUBMAP;
val _ = show "walkstar_walk_SUBMAP_typed" unifPropsTheory.walkstar_walk_SUBMAP;
val _ = show "unify_unifier_typed" unifPropsTheory.unify_unifier;
val _ = show "sunify_def_typed" rmfmapTheory.sunify_def;
val _ = show "cunify_def_typed" unifyTheory.cunify_def;
val _ = show "cunify_thm_typed" (DISCH_ALL unifyTheory.cunify_thm);
val _ = show "cunify_preserves_cwfs_typed" unifyTheory.cunify_preserves_cwfs;
val _ = show "cwalkstar_def_typed" unifyTheory.cwalkstar_def;
val _ = show "cunify_unifier_typed" unifyTheory.cunify_unifier;
val _ = show "t_unify_unifier_typed" unifyTheory.t_unify_unifier;
val _ = show "t_walk_vwalk_id_typed" unifyTheory.t_walk_vwalk_id;
val _ = show "t_walk_walk_id_typed" unifyTheory.t_walk_walk_id;
val _ = show "cunifyl_def_typed" unifyTheory.cunifyl_def;
val _ = show "cunifyl_thm_typed" unifyTheory.cunifyl_thm;
val _ = show "apply_cunif_NONE_typed" unifyTheory.apply_cunif_NONE;
val _ = show "kcunifywl_tcallish_typed" unifyTheory.kcunifywl_tcallish;
val _ = show "kcunifywl_cleaned_typed" unifyTheory.kcunifywl_cleaned;
val _ = show "tcunify_def_typed" unifyTheory.tcunify_def;
val _ = show "tcunify_correct_typed" unifyTheory.tcunify_correct;
val _ = show "fm2sp_def_typed" fmspTheory.fm2sp_def;
val _ = show "wf_fm2sp_typed" fmspTheory.wf_fm2sp;
val _ = show "lookup_fm2sp_typed" fmspTheory.lookup_fm2sp;
val _ = show "fm2sp_sp2fm_typed" fmspTheory.fm2sp_sp2fm;
val _ = show "SUBMAP_FDOM_SUBSET_typed" finite_mapTheory.SUBMAP_FDOM_SUBSET;
val _ = show "EQ_FDOM_SUBMAP_typed" finite_mapTheory.EQ_FDOM_SUBMAP;
val _ = show "walk_rangevars_typed" tcallUnifTheory.walk_rangevars;
val _ = show "tcvwalk_substvars_typed" unifyTheory.tcvwalk_substvars;
val _ = show "tcwalk_rangevars_typed" unifyTheory.tcwalk_rangevars;
val _ = show "TC_mlt1_FINITE_BAG_typed" bagTheory.TC_mlt1_FINITE_BAG;
val _ = show "TC_mlt1_UNION2_I_typed" bagTheory.TC_mlt1_UNION2_I;
val _ = show "TC_mlt1_UNION1_I_typed" bagTheory.TC_mlt1_UNION1_I;
val _ = show "walkstarR_def_typed" walkstarTheory.walkstarR_def;
val _ = show "walkstar_th1_typed" walkstarTheory.walkstar_th1;
val _ = show "walkstar_th2_typed" walkstarTheory.walkstar_th2;
val _ = show "walkstar_thWF_typed" walkstarTheory.walkstar_thWF;
val _ = show "WF_kcocwlR_typed" unifyTheory.WF_kcocwlR;
val _ = show "walkstarR_trans_typed" unifyTheory.walkstarR_trans;
val _ = show "subterm_def_typed" unifyTheory.subterm_def;
val _ = show "subterm_thm_typed" unifyTheory.subterm_thm;
val _ = show "subterm_pair_count_typed" unifyTheory.subterm_pair_count;
val _ = show "subterm_REFL_typed" unifyTheory.subterm_REFL;
val _ = show "subterm_TRANS_typed" unifyTheory.subterm_TRANS;
val _ = show "subterm_walkstarR_typed" unifyTheory.subterm_walkstarR;
val _ = show "walkstar_opth_typed" unifyTheory.walkstar_opth;
val _ = show "MEM_subterm_encode_typed" unifyTheory.MEM_subterm_encode;
val _ = show "rangevars_def_typed" substTheory.rangevars_def;
val _ = show "FINITE_rangevars_typed" substTheory.FINITE_rangevars;
val _ = show "substvars_def_typed" substTheory.substvars_def;
val _ = show "FINITE_substvars_typed" substTheory.FINITE_substvars;
val _ = show "allvars_def_typed" unifDefTheory.allvars_def;
val _ = show "FINITE_allvars_typed" unifDefTheory.FINITE_allvars;
val _ = show "allvars_sym_typed" unifDefTheory.allvars_sym;
val _ = show "uR_def_typed" unifDefTheory.uR_def;
val _ = show "uR_lex_def_typed" unifDefTheory.uR_lex_def;
val _ = show "uR_RSUBSET_uR_lex_typed" unifDefTheory.uR_RSUBSET_uR_lex;
val _ = show "WF_FINITE_PSUBSET_typed" unifDefTheory.WF_FINITE_PSUBSET;
val _ = show "WF_uR_typed" unifDefTheory.WF_uR;
val _ = show "unify_same_typed" unifPropsTheory.unify_same;
val _ = show "IN_FRANGE_rangevars_typed" substTheory.IN_FRANGE_rangevars;
val _ = show "vwalk_to_Pair_SUBSET_rangevars_typed" unifDefTheory.vwalk_to_Pair_SUBSET_rangevars;
val _ = show "allvars_SUBSET_typed" unifDefTheory.allvars_SUBSET;
val _ = show "walkstar_subterm_smaller_typed" unifDefTheory.walkstar_subterm_smaller;
val _ = show "rangevars_FUPDATE_typed" substTheory.rangevars_FUPDATE;
val _ = show "vwalk_IN_FRANGE_typed" walkTheory.vwalk_IN_FRANGE;
val _ = show "walk_to_var_typed" walkTheory.walk_to_var;
val _ = show "walk_IN_FRANGE_typed" walkTheory.walk_IN_FRANGE;
val _ = show "allvars_SUBSET_FUPDATE_typed" unifDefTheory.allvars_SUBSET_FUPDATE;
val _ = show "walkstar_subterm_FUPDATE_typed" unifDefTheory.walkstar_subterm_FUPDATE;
val _ = show "walkstar_walk_typed" walkstarTheory.walkstar_walk;
val _ = show "uP_def_typed" unifDefTheory.uP_def;
val _ = show "uP_sym_typed" unifDefTheory.uP_sym;
val _ = show "uP_FUPDATE_typed" unifDefTheory.uP_FUPDATE;
val _ = show "tca_thm_typed" unifDefTheory.tca_thm;
val _ = show "uR_subterm_typed" unifDefTheory.uR_subterm;
val _ = show "uR_subterm_FUPDATE_typed" unifDefTheory.uR_subterm_FUPDATE;
val _ = show "uR_IMP_uP_typed" unifDefTheory.uR_IMP_uP;
val _ = show "walk_SUBMAP_typed" unifDefTheory.walk_SUBMAP;
val _ = show "uP_IMP_subterm_uR_typed" unifDefTheory.uP_IMP_subterm_uR;
val _ = show "atom_axiom_typed" unifyTheory.atom_Axiom;
val _ = show "encode_infer_t_def_typed" unifyTheory.encode_infer_t_def;
val _ = show "decode_infer_t_def_typed" unifyTheory.decode_infer_t_def;
val _ = show "encode_infer_t_11_typed" unifyTheory.encode_infer_t_11;
val _ = show "decode_left_inverse_typed" unifyTheory.decode_left_inverse;
val _ = show "decode_left_inverse_I_typed" unifyTheory.decode_left_inverse_I;
val _ = show "encode_eq_var_typed" unifyTheory.encode_eq_var;
val _ = show "vR_def_typed" substTheory.vR_def;
val _ = show "wfs_def_typed" substTheory.wfs_def;
val _ = show "wfs_SUBMAP_typed" substTheory.wfs_SUBMAP;
val _ = show "wfs_no_cycles_typed" substTheory.wfs_no_cycles;
val _ = show "TC_vR_update_typed" unifDefTheory.TC_vR_update;
val _ = show "wfs_extend_typed" unifDefTheory.wfs_extend;
val _ = show "vwalk_FDOM_typed" unifDefTheory.vwalk_FDOM;
val _ = show "TC_vR_vars_walkstar_typed" walkstarTheory.TC_vR_vars_walkstar;
val _ = show "NOT_FDOM_walkstar_typed" walkstarTheory.NOT_FDOM_walkstar;
val _ = show "oc_rules_typed" walkstarTheory.oc_rules;
val _ = show "oc_walking_typed" walkstarTheory.oc_walking;
val _ = show "oc_eq_vars_walkstar_typed" walkstarTheory.oc_eq_vars_walkstar;
val _ = show "vwalk_def_typed" walkTheory.vwalk_def;
val _ = show "NOT_FDOM_vwalk_typed" walkTheory.NOT_FDOM_vwalk;
val _ = show "vwalk_to_var_typed" walkTheory.vwalk_to_var;
val _ = show "vwalk_vR_typed" walkTheory.vwalk_vR;
val _ = show "walkstar_def_typed" walkstarTheory.walkstar_def;
val _ = show "t_vars_def_typed" unifyTheory.t_vars_def;
val _ = show "t_wfs_def_typed" unifyTheory.t_wfs_def;
val _ = show "t_vR_def_typed" unifyTheory.t_vR_def;
val _ = show "t_vR_eqn_typed" unifyTheory.t_vR_eqn;
val _ = show "t_wfs_eqn_typed" unifyTheory.t_wfs_eqn;
val _ = show "t_wfs_SUBMAP_typed" unifyTheory.t_wfs_SUBMAP;
val _ = show "t_vwalk_eqn_typed" unifyTheory.t_vwalk_eqn;

(* Replay the local theorem, which is not exported by unifyTheory. *)
open unifyTheory walkTheory substTheory finite_mapTheory;
val encode_pair_cases_replay = Q.prove (
  `!t t1 t2.
    encode_infer_t t = Pair t1 t2 ==>
    (t1 = Const Tapp_tag) /\
    (?tc ts. t2 = Pair (Const (TC_tag tc)) (encode_infer_ts ts))`,
  Cases >> rw [encode_infer_t_def] >> PROVE_TAC[]);
val _ = show "encode_pair_cases_replay_typed" encode_pair_cases_replay;
(* This local theorem's complete statement is parsed with inferred types;
   its source proof is not replayed by this capture. *)
val encode_unify_lemma_statement = ``
  !s t1 t2 s' t1' t2'.
  (s = (encode_infer_t o_f s')) /\
  (((t1 = encode_infer_t t1') /\ (t2 = encode_infer_t t2')) \/
   (?c. (t1 = Const c) /\ (t2 = Const c) /\ (t1' = t2')) \/
   (?c ts1 ts2.
     (t1 = Pair (Const c) (encode_infer_ts ts1)) /\
     (t2 = Pair (Const c) (encode_infer_ts ts2)) /\
     (t1' = Infer_Tapp ts1 ARB) /\ (t2' = Infer_Tapp ts2 ARB)) \/
   (?ts1 ts2.
      (t1 = encode_infer_ts ts1) /\ (t2 = encode_infer_ts ts2) /\
      (t1' = Infer_Tapp ts1 ARB) /\ (t2' = Infer_Tapp ts2 ARB))) /\
  t_wfs s' ==>
  (unify s t1 t2 =
   OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2'))``;
val _ = (print "encode_unify_lemma_statement_typed=";
         print_term encode_unify_lemma_statement; print "\n");
val encode_vwalk_replay = Q.prove (
  `!s. t_wfs s ==> !u. vwalk (encode_infer_t o_f s) u = encode_infer_t (t_vwalk s u)`,
  NTAC 2 STRIP_TAC >>
  ho_match_mp_tac t_vwalk_ind >>
  rw [] >>
  `wfs (encode_infer_t o_f s)` by metis_tac[t_wfs_def] >>
  rw [Once vwalk_def] >>
  rw [Once t_vwalk_eqn, FLOOKUP_o_f] >>
  Cases_on `FLOOKUP s u` >>
  rw [encode_infer_t_def] >>
  Cases_on `x` >>
  rw [encode_infer_t_def]);
val _ = show "encode_vwalk_replay_typed" encode_vwalk_replay;
val _ = show "t_walk_def_typed" unifyTheory.t_walk_def;
val _ = show "t_walk_eqn_typed" unifyTheory.t_walk_eqn;
val _ = show "t_oc_def_typed" unifyTheory.t_oc_def;
val _ = show "t_oc_eqn_typed" unifyTheory.t_oc_eqn;
val _ = show "t_ext_s_check_def_typed" unifyTheory.t_ext_s_check_def;
val _ = show "t_ext_s_check_eqn_typed" unifyTheory.t_ext_s_check_eqn;
val _ = show "t_unify_def_typed" unifyTheory.t_unify_def;
val _ = show "ts_unify_def_typed" unifyTheory.ts_unify_def;
val _ = show "t_unify_eqn_typed" unifyTheory.t_unify_eqn;
val _ = show "t_unify_wfs_typed" unifyTheory.t_unify_wfs;
val _ = show "oc_tvar_db_typed" unifyTheory.oc_tvar_db;
val _ = show "oc_unit_typed" unifyTheory.oc_unit;
val _ = show "t_walkstar_eqn_typed" unifyTheory.t_walkstar_eqn;

open walkstarTheory;
val encode_walk_replay = Q.prove (
  `!s. t_wfs s ==> !t. walk (encode_infer_t o_f s) (encode_infer_t t) = encode_infer_t (t_walk s t)`,
  rw [walk_def] >>
  imp_res_tac encode_vwalk_replay >>
  fs [] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw [t_walk_def, decode_left_inverse] >>
  metis_tac [decode_left_inverse]);
val _ = show "encode_walk_replay_typed" encode_walk_replay;

val ts_walkstar_replay = Q.prove (
  `!l s. t_wfs s ==> (decode_infer_ts ((encode_infer_t o_f s) ◁ encode_infer_ts l) = MAP (t_walkstar s) l)`,
  Induct_on `l` >>
  rw [t_wfs_def, encode_infer_t_def, Once walkstar_def, decode_infer_t_def] >>
  rw [t_walkstar_def]);
val _ = show "ts_walkstar_replay_typed" ts_walkstar_replay;
val _ = show "wfs_FEMPTY_typed" substTheory.wfs_FEMPTY;
val _ = show "walkstar_FEMPTY_typed" walkstarTheory.walkstar_FEMPTY;
val _ = show "t_walkstar_FEMPTY_typed" unifyTheory.t_walkstar_FEMPTY;
val _ = show "t_vars_eqn_typed" unifyTheory.t_vars_eqn;
val _ = show "t_vwalk_to_var_typed" unifyTheory.t_vwalk_to_var;
val _ = show "t_walkstar_ind_typed" unifyTheory.t_walkstar_ind;
val _ = show "t_walkstar_vars_notin_typed" unifyTheory.t_walkstar_vars_notin;
val _ = show "t_walkstar_tuvar_props_typed" unifyTheory.t_walkstar_tuvar_props;
val _ = show "t_walkstar_idempotent_typed" unifyTheory.t_walkstar_idempotent;
val _ = show "vwalk_SUBMAP_typed" walkTheory.vwalk_SUBMAP;
val _ = show "walkstar_ind_discharged_typed" (DISCH_ALL walkstarTheory.walkstar_ind);
val _ = show "walkstar_SUBMAP_typed" walkstarTheory.walkstar_SUBMAP;

(* Replay the local inference encoding theorem in its original proof order. *)
val encode_walkstar_replay = Q.prove (
  `!s t. t_wfs s ==> walkstar (encode_infer_t o_f s) (encode_infer_t t) = encode_infer_t (t_walkstar s t)`,
  rw [] >>
  imp_res_tac t_walkstar_ind >>
  Q.SPEC_TAC (`t`,`t`) >>
  pop_assum ho_match_mp_tac >>
  rw [] >>
  rw [Once t_walkstar_eqn] >>
  `wfs (encode_infer_t o_f s)` by fs [t_wfs_def] >>
  rw [Once walkstar_def] >>
  rw [Once encode_walk_replay] >>
  Cases_on `t_walk s t` >>
  rw [encode_infer_t_def] >>
  pop_assum mp_tac >>
  pop_assum (fn _ => all_tac) >>
  Induct_on `l` >>
  rw [encode_infer_t_def] >>
  rw [Once walkstar_def]);
val _ = show "encode_walkstar_replay_typed" encode_walkstar_replay;
val _ = show "t_walkstar_SUBMAP_typed" unifyTheory.t_walkstar_SUBMAP;
val _ = show "t_compat_def_typed" unifyTheory.t_compat_def;
val _ = show "t_compat_refl_typed" unifyTheory.t_compat_refl;
val _ = show "t_compat_trans_typed" unifyTheory.t_compat_trans;
val _ = show "SUBMAP_t_compat_typed" unifyTheory.SUBMAP_t_compat;
val _ = show "cvwalk_code_def_typed" unifyTheory.cvwalk_code_def;
val _ = show "TAILCALL_def_typed" WhileTheory.TAILCALL_def;
val _ = show "cvwalk_tcallish_typed" unifyTheory.cvwalk_tcallish;
val _ = show "tcvwalk_def_typed" unifyTheory.tcvwalk_def;
val _ = show "tcvwalk_thm_typed" unifyTheory.tcvwalk_thm;
val _ = show "tcvwalk_correct_typed" unifyTheory.tcvwalk_correct;
val _ = show "tcwalk_def_typed" unifyTheory.tcwalk_def;
val _ = show "tcwalk_correct_typed" unifyTheory.tcwalk_correct;
val _ = show "tcwalk_EQ_Infer_Tuvar_typed" unifyTheory.tcwalk_EQ_Infer_Tuvar;
val _ = show "kcocwl_code_def_typed" unifyTheory.kcocwl_code_def;
val _ = show "kcocwl_preserves_precond_typed" unifyTheory.kcocwl_preserves_precond;
val _ = show "kcocwl_def_typed" unifyTheory.kcocwl_def;
val _ = show "kcocwl_tcallish_typed" unifyTheory.kcocwl_tcallish;
val _ = show "kcocwl_cleaned_typed" unifyTheory.kcocwl_cleaned;
val _ = show "tcocwl_correct0_typed" unifyTheory.tcocwl_correct0;
val _ = show "kcocwlR_def_typed" unifyTheory.kcocwlR_def;
val _ = show "kcocwl_ensures_decrease_typed" unifyTheory.kcocwl_ensures_decrease;
val _ = show "tcocwl_thm_typed" unifyTheory.tcocwl_thm;
val _ = show "soc_encode_ts_typed" unifyTheory.soc_encode_ts;
val _ = show "coc_thm_typed" (DISCH_ALL unifyTheory.coc_thm);
val _ = show "cocl_def_typed" unifyTheory.cocl_def;
val _ = show "cocl_EXISTS_typed" unifyTheory.cocl_EXISTS;
val _ = show "coc_thm_prime_typed" (DISCH_ALL unifyTheory.coc_thm');
val _ = show "tcocwl_correct_typed" unifyTheory.tcocwl_correct;
val _ = show "kcwalkstarwl_code_def_typed" unifyTheory.kcwalkstarwl_code_def;
val _ = show "star_kwork_def_typed" unifyTheory.star_kwork_def;
val _ = show "star_workbag_def_typed" unifyTheory.star_workbag_def;
val _ = show "FINITE_star_kwork_typed" unifyTheory.FINITE_star_kwork;
val _ = show "FINITE_star_workbag_typed" unifyTheory.FINITE_star_workbag;
val _ = show "isCONSk_def_typed" unifyTheory.isCONSk_def;
val _ = show "kcwalkstarwlR_def_typed" unifyTheory.kcwalkstarwlR_def;
val _ = show "WF_kcwalkstarwlR_typed" unifyTheory.WF_kcwalkstarwlR;
val _ = show "kcwalkstarwl_ensures_decrease_typed" unifyTheory.kcwalkstarwl_ensures_decrease;
val _ = show "kcwalkstarwl_preserves_precond_typed" unifyTheory.kcwalkstarwl_preserves_precond;
val _ = show "kclkont_axiom_typed" unifyTheory.kclkont_Axiom;
val _ = show "tcwalkstarwl_thm_typed" unifyTheory.tcwalkstarwl_thm;
val _ = show "tcwalkstarwl_correct_typed" unifyTheory.tcwalkstarwl_correct;
val _ = show "cunify_code_def_typed" unifyTheory.cunify_code_def;
val _ = show "kcunifywl_preserves_precond_typed" unifyTheory.kcunifywl_preserves_precond;
val _ = show "kcunifywl_ensures_decrease_typed" unifyTheory.kcunifywl_ensures_decrease;
val _ = show "isvars_def_typed" unifyTheory.isvars_def;
val _ = show "FINITE_isvars_typed" unifyTheory.FINITE_isvars;
val _ = show "cplist_vars_def_typed" unifyTheory.cplist_vars_def;
val _ = show "FINITE_cplist_vars_typed" unifyTheory.FINITE_cplist_vars;
val _ = show "vars_encode_infer_ts_typed" unifyTheory.vars_encode_infer_ts;
val _ = show "vars_walkstar_encode_infer_ts_typed" unifyTheory.vars_walkstar_encode_infer_ts;
val _ = show "PFLAT_def_typed" unifyTheory.PFLAT_def;
val _ = show "BAG_INSERT_commutes_typed" bagTheory.BAG_INSERT_commutes;
val _ = show "BAG_UNION_INSERT_typed" bagTheory.BAG_UNION_INSERT;
val _ = show "PFLAT_CONS2_typed" unifyTheory.PFLAT_CONS2;
val _ = show "PFLAT_NIL1_typed" unifyTheory.PFLAT_NIL1;
val _ = show "PFLAT_eqn_typed" unifyTheory.PFLAT_eqn;
val _ = show "FINITE_BAG_PFLAT_typed" unifyTheory.FINITE_BAG_PFLAT;
val _ = show "FINITE_BAG_FOLDR_INSERT_typed" unifyTheory.FINITE_BAG_FOLDR_INSERT;
val _ = show "FOLDR_BAG_INSERT_UNION_typed" unifyTheory.FOLDR_BAG_INSERT_UNION;
val _ = show "BAG_IN_BAG_OF_LIST_typed" unifyTheory.BAG_IN_BAG_OF_LIST;
val _ = show "kcunifywlR_def_typed" unifyTheory.kcunifywlR_def;
val _ = show "WF_kcunifywlR_typed" unifyTheory.WF_kcunifywlR;
val _ = show "tcunify_thm_typed" unifyTheory.tcunify_thm;
val _ = show "sp2fm_def_typed" fmspTheory.sp2fm_def;
val _ = show "FLOOKUP_sp2fm_typed" fmspTheory.FLOOKUP_sp2fm;
val _ = show "sp2fm_thm_typed" fmspTheory.sp2fm_thm;
val _ = show "swfs_def_typed" rmfmapTheory.swfs_def;
val _ = show "cwfs_def_typed" unifyTheory.cwfs_def;
val _ = show "cwfs_insert_tvar_db_typed" unifyTheory.cwfs_insert_tvar_db;
val _ = show "cwfs_var2_extend_typed" unifyTheory.cwfs_var2_extend;
val _ = show "cvwalk_preserves_precond_typed" unifyTheory.cvwalk_preserves_precond;
(* These source theorem values carry HOL assumptions; retain them as premises. *)
val _ = show "cvwalk_thm_typed" (DISCH_ALL unifyTheory.cvwalk_thm);
val _ = show "cwalk_thm_typed" (DISCH_ALL unifyTheory.cwalk_thm);
val _ = show "sp2fm_map_typed" unifyTheory.sp2fm_map;
val _ = show "cvwalkR_def_typed" unifyTheory.cvwalkR_def;
val _ = show "cvwalk_ensures_decrease_typed" unifyTheory.cvwalk_ensures_decrease;
val _ = show "WF_cvwalkR_typed" unifyTheory.WF_cvwalkR;
