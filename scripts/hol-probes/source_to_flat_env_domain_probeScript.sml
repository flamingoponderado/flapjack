load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
val _ = print "env_domain_type=";
val _ = print_type (type_of ``source_to_flatProof$env_domain_eq``);
val _ = print "\n";
val _ = print "env_domain_definition=";
val _ = print_term (concl source_to_flatProofTheory.env_domain_eq_def);
val _ = print "\n";

(* Replay the original local theorem, which is not exported by its theory. *)
open source_to_flatProofTheory source_to_flatTheory semanticPrimitivesTheory
  namespacePropsTheory namespaceTheory pred_setTheory pairTheory optionTheory;
val local_append = Q.prove (
  `env_domain_eq env1 env1' ∧ env_domain_eq env2 env2' ⇒
   env_domain_eq (extend_env env1 env2) (extend_dec_env env1' env2')`,
  rw [env_domain_eq_def, extend_env_def, extend_dec_env_def,
      nsLookupMod_nsAppend_some, nsLookup_nsAppend_some, nsLookup_nsDom,
      nsDomMod_def, EXTENSION, GSPECIFICATION, EXISTS_PROD] >>
  metis_tac [option_nchotomy, NOT_SOME_NONE, pair_CASES]);
val _ = if null (hyp local_append) then () else raise Fail "local theorem has hypotheses";
val _ = print "env_domain_append=";
val _ = print_term (concl local_append);
val _ = print "\n";

(* Replay the local global invariant theorem with the original proof. *)
val local_global_append = Q.prove (
  `!genv var_map1 var_map2 env1 env2.
    env_domain_eq var_map1 env1 ∧
    global_env_inv genv var_map1 {} env1 ∧
    global_env_inv genv var_map2 {} env2 ⇒
    global_env_inv genv (extend_env var_map1 var_map2) {} (extend_dec_env env1 env2)`,
  rw [env_domain_eq_def, v_rel_global_eqn, nsLookup_nsAppend_some,
    extend_env_def, extend_dec_env_def] >>
  first_x_assum drule >>
  rw [] >> rw []
  >- (
    goal_assum (first_assum o mp_then (Pat `EL _ _ = _`) mp_tac) >>
    rw [] >>
    fs [EXTENSION, namespacePropsTheory.nsLookup_nsDom,
        namespaceTheory.nsDomMod_def, GSPECIFICATION, EXISTS_PROD] >>
    metis_tac [NOT_SOME_NONE, option_nchotomy]
  )
  >- (
    qsuff_tac `nsLookup var_map1.c x = NONE`
    >- (
      fs [EXTENSION, namespacePropsTheory.nsLookup_nsDom,
          namespaceTheory.nsDomMod_def, GSPECIFICATION, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy]
    ) >>
    fs [EXTENSION, namespacePropsTheory.nsLookup_nsDom] >>
    metis_tac [NOT_SOME_NONE, option_nchotomy]
  ));
val _ = if null (hyp local_global_append) then () else raise Fail "local theorem has hypotheses";
val _ = print "global_env_inv_append_typed=";
val _ = print_term (concl local_global_append);
val _ = print "\n";
