(* Replay environment-conversion declarations and initialization facts from
   envRelScript.sml and repl_typesScript.sml without building those theories. *)
load "inferPropsTheory";
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

val lookup_varE_empty_replay = Q.prove(
  `!x. lookup_varE x Empty = NONE`,
  rw [lookup_varE_def, tveLookup_def] \\ every_case_tac);
val _ = show "lookup_varE_empty_replay_typed" lookup_varE_empty_replay;

val init_config_tenv_to_ienv_replay = Q.prove(
  `init_config = probe_tenv_to_ienv prim_tenv`,
  rw [init_config_def, probe_tenv_to_ienv_def] \\ EVAL_TAC);
val _ = show "init_config_tenv_to_ienv_replay_typed" init_config_tenv_to_ienv_replay;
