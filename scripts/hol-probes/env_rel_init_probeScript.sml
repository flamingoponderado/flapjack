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

val lookup_varE_empty_replay = Q.prove(
  `!x. lookup_varE x Empty = NONE`,
  rw [lookup_varE_def, tveLookup_def] \\ every_case_tac);
val _ = show "lookup_varE_empty_replay_typed" lookup_varE_empty_replay;

val init_config_tenv_to_ienv_replay = Q.prove(
  `init_config = probe_tenv_to_ienv prim_tenv`,
  rw [init_config_def, probe_tenv_to_ienv_def] \\ EVAL_TAC);
val _ = show "init_config_tenv_to_ienv_replay_typed" init_config_tenv_to_ienv_replay;
