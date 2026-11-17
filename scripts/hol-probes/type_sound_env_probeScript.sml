(* Typed declarative environment invariants used by compilerProof$type_config_ok. *)
load "typeSoundInvariantsTheory";
load "primTypesTheory";
open HolKernel Parse boolLib bossLib;
open typeSoundInvariantsTheory primTypesTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "tenv_abbrev_ok_def_typed" typeSoundInvariantsTheory.tenv_abbrev_ok_def;
val _ = show "tenv_ctor_ok_def_typed" typeSoundInvariantsTheory.tenv_ctor_ok_def;
val _ = show "tenv_val_ok_def_typed" typeSoundInvariantsTheory.tenv_val_ok_def;
val _ = show "tenv_ok_def_typed" typeSoundInvariantsTheory.tenv_ok_def;
(* Replay the proof from repl_typesScript.sml without building that theory in
   the read-only source checkout. *)
val tenv_ok_prim_tenv_replay = Q.prove(
  `tenv_ok prim_tenv`,
  EVAL_TAC \\ rw[] \\ Cases_on`id` \\
  fs[namespaceTheory.nsLookup_def] \\ pop_assum mp_tac \\
  rw[] \\ rw[] \\ EVAL_TAC);
val _ = show "tenv_ok_prim_tenv_replay_typed" tenv_ok_prim_tenv_replay;
