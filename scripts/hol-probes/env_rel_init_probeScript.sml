(* Replay environment-conversion declarations and initialization facts from
   envRelScript.sml and repl_typesScript.sml without building those theories. *)
load "inferPropsTheory";
load "namespacePropsTheory";
load "primTypesTheory";
load "preamble";
open HolKernel Parse boolLib bossLib;
open preamble inferPropsTheory inferTheory typeSystemTheory primTypesTheory;
val _ = new_theory "flapjack_env_rel_init_replay";
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

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
val _ = show "extend_dec_ienv_typed" inferTheory.extend_dec_ienv_def;

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

val check_freevars_empty_convert_unconvert_id_replay = Q.prove(
  `!t. check_freevars n [] t ⇒ probe_convert_t (unconvert_t t) = t`,
  ho_match_mp_tac unconvert_t_ind >>
  rw [] >> fs [unconvert_t_def, probe_convert_t_def, check_freevars_def] >>
  fs [MAP_MAP_o, MAP_EQ_ID, EVERY_MEM]);
val _ = show "check_freevars_empty_convert_unconvert_id_replay_typed"
  check_freevars_empty_convert_unconvert_id_replay;

val infer_type_subst_nil_replay = Q.prove(
  `(∀t. check_freevars n [] t ⇒ infer_type_subst [] t = unconvert_t t) ∧
   (∀ts. EVERY (check_freevars n []) ts ⇒ MAP (infer_type_subst []) ts = MAP unconvert_t ts)`,
  ho_match_mp_tac (TypeBase.induction_of ``:t``) >>
  rw [infer_type_subst_alt, unconvert_t_def, check_freevars_def] >>
  fsrw_tac [boolSimps.ETA_ss] []);
val _ = show "infer_type_subst_nil_replay_typed" infer_type_subst_nil_replay;

val lookup_varE_empty_replay = Q.prove(
  `!x. lookup_varE x Empty = NONE`,
  rw [lookup_varE_def, tveLookup_def] \\ every_case_tac);
val _ = show "lookup_varE_empty_replay_typed" lookup_varE_empty_replay;

val init_config_tenv_to_ienv_replay = Q.prove(
  `init_config = probe_tenv_to_ienv prim_tenv`,
  rw [init_config_def, probe_tenv_to_ienv_def] \\ EVAL_TAC);
val _ = show "init_config_tenv_to_ienv_replay_typed" init_config_tenv_to_ienv_replay;
