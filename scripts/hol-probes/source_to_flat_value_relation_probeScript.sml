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
val _ = show_thm "value_rel_induction=" source_to_flatProofTheory.v_rel_ind;
val _ = show_thm "value_rel_cases=" source_to_flatProofTheory.v_rel_cases;
val _ = show_thm "env_rel_LIST_REL=" source_to_flatProofTheory.env_rel_LIST_REL;
val _ = show_thm "env_all_rel_cases_typed=" source_to_flatProofTheory.env_all_rel_cases;
val _ = show_thm "v_rel_global_eqn_typed=" source_to_flatProofTheory.v_rel_global_eqn;

(* Replay the original local case-equation construction. *)
open source_to_flatProofTheory;
val v_rel_global_eqn_replay = SIMP_CONV (srw_ss ()) [Once v_rel_cases]
  ``global_env_inv genv comp_map shadowers env``;
val _ = show_thm "v_rel_global_eqn_replay=" v_rel_global_eqn_replay;
val local_eqns =
  [``v_rel genv (Litv l) v``, ``v_rel genv (Conv cn vs) v``,
   ``v_rel genv (Loc b l) v``, ``v_rel genv (Vectorv vs) v``,
   ``env_rel genv nsEmpty env'``, ``env_rel genv (nsBind x v env) env'``,
   ``v_rel genv (Env e id) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> map GEN_ALL |> LIST_CONJ;
val _ = show_thm "v_rel_eqns_local=" local_eqns;
val local_eqns_non_global =
  local_eqns |> BODY_CONJUNCTS
    |> filter (null o find_terms (can (match_term ``global_env_inv``)) o concl)
    |> map GEN_ALL |> LIST_CONJ;
val _ = show_thm "v_rel_eqns_non_global_replay=" local_eqns_non_global;

(* Parse the original local do_opapp statement; its proof depends on local
   source-script declarations not exported by source_to_flatProofTheory. *)
val do_opapp_local_statement =
  ``!genv vs vs_i1 env e.
      semanticPrimitives$do_opapp vs = SOME (env, e) /\
      LIST_REL (source_to_flatProof$v_rel genv) vs vs_i1 ==>
      ?comp_map env_i1 locals t1 ts.
        source_to_flatProof$env_all_rel genv comp_map env env_i1 locals /\
        LENGTH ts = LENGTH locals /\
        flatSem$do_opapp vs_i1 = SOME
          (env_i1, source_to_flat$compile_exp t1
            (comp_map with v := source_to_flatProof$bind_locals ts locals comp_map.v) e)``;
val _ = (print "do_opapp_local_statement="; print_term do_opapp_local_statement; print "\n");
