load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_type label tm = (print label; print_type (type_of tm); print "\n");
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_type "value_rel_type=" ``source_to_flatProof$v_rel``;
val _ = show_type "env_rel_type=" ``source_to_flatProof$env_rel``;
val _ = show_type "global_inv_type=" ``source_to_flatProof$global_env_inv``;
val _ = show_thm "value_rel_rules=" source_to_flatProofTheory.v_rel_rules;
val _ = show_thm "env_rel_LIST_REL=" source_to_flatProofTheory.env_rel_LIST_REL;

(* Replay the original local case-equation construction. *)
open source_to_flatProofTheory;
val local_eqns =
  [``v_rel genv (Litv l) v``, ``v_rel genv (Conv cn vs) v``,
   ``v_rel genv (Loc b l) v``, ``v_rel genv (Vectorv vs) v``,
   ``env_rel genv nsEmpty env'``, ``env_rel genv (nsBind x v env) env'``,
   ``v_rel genv (Env e id) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> map GEN_ALL |> LIST_CONJ;
val _ = show_thm "v_rel_eqns_local=" local_eqns;
