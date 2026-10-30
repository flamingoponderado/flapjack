load "flat_to_closProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "op_globals=" closPropsTheory.op_gbag_def;
val _ = show "set_globals=" closPropsTheory.set_globals_def;
val _ = show "esgc_free=" closPropsTheory.esgc_free_def;
val _ = show "elist_globals_empty=" flat_to_closProofTheory.elist_globals_empty;
val _ = show "smartcons_globals=" flat_to_closProofTheory.set_globals_SmartCons;
val _ = show "smartcons_esgc=" flat_to_closProofTheory.esgc_free_SmartCons;
val _ = show "bag_image_definition=" bagTheory.BAG_IMAGE_DEF;
val _ = show "compile_globals=" flat_to_closProofTheory.compile_set_globals;
val _ = show "compile_decs_globals=" flat_to_closProofTheory.compile_decs_set_globals;
val _ = show "compile_eq_globals=" flat_to_closProofTheory.compile_eq_set_globals;
val _ = show "compile_esgc=" flat_to_closProofTheory.compile_esgc_free;
val _ = show "compile_decs_esgc=" flat_to_closProofTheory.compile_decs_esgc_free;
