load "preamble"; load "source_evalProofTheory";
open HolKernel Parse boolLib bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "v_rel_abs=" source_evalProofTheory.v_rel_abs;
val _ = show_thm "compiler_fun=" source_evalProofTheory.mk_compiler_fun_from_ci_def;
val _ = show_thm "init_eval=" source_evalProofTheory.mk_init_eval_state_def;
val _ = show_thm "insert=" source_evalProofTheory.insert_gen_oracle_def;
val _ = show_thm "adjust=" source_evalProofTheory.adjust_oracle_def;
val _ = show_thm "is_insert=" source_evalProofTheory.is_insert_oracle_def;
val _ = show_thm "adjust_insert=" source_evalProofTheory.adjust_oracle_insert_gen_oracle;
val _ = show_thm "adjust_evaluate=" source_evalProofTheory.adjust_oracle_evaluate;
val _ = show_thm "adjust_semantics=" source_evalProofTheory.adjust_oracle_semantics_prog;
val _ = show_thm "evaluate_induction=" evaluateTheory.full_evaluate_ind;
fun show_type label tm = (print label; print_type (type_of tm); print "\n");
val _ = show_type "ci_compiler_type=" ``\ci. ci.compiler_fun``;
val _ = show_type "ci_config_value_type=" ``\ci. ci.config_v``;
val _ = show_type "ci_config_domain_type=" ``\ci. ci.config_dom``;
val _ = show_type "ci_decs_value_type=" ``\ci. ci.decs_v``;
val _ = show_type "ci_decs_domain_type=" ``\ci. ci.decs_dom``;
val _ = show_type "ci_initial_type=" ``\ci. ci.init_state``;
val adjust_ev_decs = source_evalProofTheory.adjust_oracle_evaluate
  |> UNDISCH |> CONJUNCTS |> List.last |> DISCH_ALL
  |> SIMP_RULE bool_ss [PULL_FORALL]
  |> Q.SPEC `s with clock := k`
  |> SIMP_RULE (srw_ss ()) [];
val _ = show_thm "adjust_ev_decs_replay=" adjust_ev_decs;
val _ = show_thm "result_rel_cases=" source_evalProofTheory.result_rel_IMP_cases;
val _ = show_thm "oleast_definition=" WhileTheory.OLEAST_def;
val _ = show_thm "oleast_intro=" WhileTheory.OLEAST_INTRO;
val _ = show_thm "least_exists_imp=" WhileTheory.LEAST_EXISTS_IMP;
val _ = show_thm "recorded_oracle_wf=" source_evalProofTheory.recorded_orac_wf_def;
val _ = show_thm "oracle_state_projection=" source_evalProofTheory.orac_s_def;
val oracle_arb_application = rhs (concl (List.nth (CONJUNCTS source_evalProofTheory.orac_s_def, 1)));
val _ = show_type "oracle_arb_type=" (rator oracle_arb_application);
val _ = show_type "oracle_arb_argument_type=" (rand oracle_arb_application);
val _ = show_thm "extract_oracle=" source_evalProofTheory.extract_oracle_def;
val _ = show_thm "oracle_agrees=" source_evalProofTheory.orac_agrees_def;
val _ = show_thm "oracle_extended_wf=" source_evalProofTheory.orac_extended_wf_def;
val _ = show_thm "record_forward=" source_evalProofTheory.record_forward_def;
val _ = show_thm "record_forward_refl=" source_evalProofTheory.record_forward_refl;
val _ = show_thm "record_forward_trans=" source_evalProofTheory.record_forward_trans;
val _ = show_thm "oracle_agrees_backward=" source_evalProofTheory.orac_agrees_backward;
val _ = show_thm "value_to_nat=" source_evalProofTheory.v_to_nat_def;
val _ = show_thm "value_to_env_id=" source_evalProofTheory.v_to_env_id_def;
val _ = show_thm "do_eval_record=" source_evalProofTheory.do_eval_record_def;
val _ = show_thm "is_record=" source_evalProofTheory.is_record_def;
val _ = show_thm "is_record_imp=" source_evalProofTheory.is_record_IMP;
val _ = show_thm "recorded_wf_step=" source_evalProofTheory.recorded_orac_wf_step;
val _ = show_thm "value_to_nat_some=" source_evalProofTheory.v_to_nat_SOME;
val _ = show_thm "value_to_env_id_some=" source_evalProofTheory.v_to_env_id_SOME;
val _ = show_thm "value_to_list_concrete=" source_evalProofTheory.v_to_list_concrete;
val _ = show_thm "maybe_all_list_some=" source_evalProofTheory.maybe_all_list_SOME;
val _ = show_thm "maybe_all_list_every=" source_evalProofTheory.maybe_all_list_EVERY;
val _ = show_thm "word8_list_concrete=" source_evalProofTheory.v_to_word8_list_concrete;
val _ = show_thm "word64_list_concrete=" source_evalProofTheory.v_to_word64_list_concrete;
val _ = show_thm "compiler_agrees_concrete=" source_evalProofTheory.compiler_agrees;
val _ = show_thm "reset_oracle_eqs=" source_evalProofTheory.reset_env_generation_orac_eqs;
val _ = show_thm "insert_declare_env=" source_evalProofTheory.insert_declare_env;
val _ = show_thm "insert_do_eval=" source_evalProofTheory.insert_do_eval;
val record_forward_trans_sym = REWRITE_RULE [Once CONJ_COMM] source_evalProofTheory.record_forward_trans;
val _ = show_thm "record_forward_trans_sym_replay=" record_forward_trans_sym;
val _ = show_thm "evaluate_record_forward=" source_evalProofTheory.evaluate_is_record_forward;
val spt_mem_to_list_a = prove(
  ``!t acc x. MEM x (sptree$toListA acc t) <=> MEM x acc \/ ?k. sptree$lookup k t = SOME x``,
  simp [sptreeTheory.toListA_append, GSYM sptreeTheory.toList_def, sptreeTheory.MEM_toList] >> metis_tac []);
val _ = show_thm "spt_mem_to_list_a_replay=" spt_mem_to_list_a;
val _ = show_thm "spt_mem_to_list=" sptreeTheory.MEM_toList;
val _ = show_thm "spt_to_list_a_def=" sptreeTheory.toListA_def;
val _ = show_thm "spt_to_list_def=" sptreeTheory.toList_def;
val _ = show_thm "environment_relation_definition=" source_evalProofTheory.env_rel_def;
val _ = show_thm "environment_relation_monotonic=" source_evalProofTheory.env_rel_mono_rel;
val _ = show_thm "source_value_relation_rules=" source_evalProofTheory.v_rel_rules;
val _ = show_thm "source_value_relation_cases=" source_evalProofTheory.v_rel_cases;
val _ = show_thm "source_value_relation_induction=" source_evalProofTheory.v_rel_ind;
val _ = show_thm "source_value_relation_concrete=" source_evalProofTheory.v_rel_concrete_v;
val _ = show_thm "source_environment_relation_concrete=" source_evalProofTheory.env_rel_concrete_v;
val _ = show_thm "source_value_relation_left_simps=" source_evalProofTheory.v_rel_l_simps;
val _ = show_thm "source_value_relation_boolean=" source_evalProofTheory.v_rel_Boolv;
val _ = show_thm "source_state_relation_definition=" source_evalProofTheory.s_rel_def;
val _ = show_thm "source_environment_forward_definition=" source_evalProofTheory.es_forward_def;
val _ = show_thm "source_environment_forward_refl=" source_evalProofTheory.es_forward_refl;
val _ = show_thm "source_environment_forward_trans=" source_evalProofTheory.es_forward_trans;
val _ = show_thm "source_value_relation_forward=" source_evalProofTheory.v_rel_forward;
val _ = show_thm "store_value_relation_monotonic=" semanticPrimitivesPropsTheory.sv_rel_mono;
val _ = show_thm "source_forward_rules=" source_evalProofTheory.forward_rules;
