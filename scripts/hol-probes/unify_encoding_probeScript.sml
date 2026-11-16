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
val _ = show "TC_vR_vars_walkstar_typed" walkstarTheory.TC_vR_vars_walkstar;
val _ = show "NOT_FDOM_walkstar_typed" walkstarTheory.NOT_FDOM_walkstar;
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
val _ = show "tcvwalk_def_typed" unifyTheory.tcvwalk_def;
val _ = show "tcvwalk_thm_typed" unifyTheory.tcvwalk_thm;
val _ = show "tcvwalk_correct_typed" unifyTheory.tcvwalk_correct;
val _ = show "tcwalk_def_typed" unifyTheory.tcwalk_def;
val _ = show "tcwalk_correct_typed" unifyTheory.tcwalk_correct;
val _ = show "tcwalk_EQ_Infer_Tuvar_typed" unifyTheory.tcwalk_EQ_Infer_Tuvar;
val _ = show "cunify_code_def_typed" unifyTheory.cunify_code_def;
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
