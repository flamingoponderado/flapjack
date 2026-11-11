(* Typed source declarations for the substitution functions and inference
   environment in cakeml/compiler/inference/inferScript.sml. *)
load "inferTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "infer_type_subst_def_typed" inferTheory.infer_type_subst_def;
val _ = show "infer_deBruijn_subst_def_typed" inferTheory.infer_deBruijn_subst_def;
val _ = show "inf_env_axiom_typed" inferTheory.inf_env_Axiom;
val _ = show "init_config_def_typed" inferTheory.init_config_def;
