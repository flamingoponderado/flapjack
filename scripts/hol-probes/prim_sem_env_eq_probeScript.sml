(* Replay primSemEnvScript.sml's EVAL theorem from the pinned source. *)
load "preamble";
load "primTypesTheory";
load "evaluateComputeLib";
open HolKernel Parse boolLib bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = (print "prim_sem_env_eq_typed=";
  print_thm (EVAL ``primTypes$prim_sem_env (ffi:'ffi ffi_state)``); print "\n");
