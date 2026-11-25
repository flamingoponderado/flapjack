(* Typed captures for the typeSysProps reviewed rows (task 273). *)
load "preamble";
load "typeSysPropsTheory";
open HolKernel Parse boolLib bossLib;
open preamble typeSysPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = (print (label ^ "=");
  app (fn h => (print_term h; print " ==> ")) (hyp th);
  print_term (concl th); print "\n");

val _ = show "tenv_val_ok_nsEmpty_typed" typeSysPropsTheory.tenv_val_ok_nsEmpty;
val _ = show "tenv_ctor_ok_nsEmpty_typed" typeSysPropsTheory.tenv_ctor_ok_nsEmpty;
val _ = show "tenv_abbrev_ok_nsEmpty_typed" typeSysPropsTheory.tenv_abbrev_ok_nsEmpty;
val _ = show "tenv_ok_empty_typed" typeSysPropsTheory.tenv_ok_empty;
val _ = show "unchanged_tenv_typed" typeSysPropsTheory.unchanged_tenv;
