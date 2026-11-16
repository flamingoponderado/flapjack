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
