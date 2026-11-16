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
