load "preamble"; load "source_evalProofTheory";
open HolKernel Parse boolLib bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_term label tm = (print label; print_term tm; print "\n");
val s_rel_clock2_replay = prove (
  ``!k. source_evalProof$s_rel ci s t ==>
      source_evalProof$s_rel ci (s with clock := k) (t with clock := k)``,
  rw [source_evalProofTheory.s_rel_def] >>
  simp [semanticPrimitivesTheory.state_component_equality]);
val _ = if null (hyp s_rel_clock2_replay) then () else raise Fail "s_rel_clock2 hypotheses";
val _ = show_term "s_rel_clock2_replay=" (concl s_rel_clock2_replay);
val extract_oracle_some_suc_replay = prove (
  ``IS_SOME (source_evalProof$extract_oracle s env decs (SUC i)) ==>
    IS_SOME (source_evalProof$extract_oracle s env decs i)``,
  simp [source_evalProofTheory.extract_oracle_def] >>
  DEEP_INTRO_TAC WhileTheory.OLEAST_INTRO >>
  DEEP_INTRO_TAC WhileTheory.OLEAST_INTRO >>
  rw [] >> simp [UNCURRY] >> res_tac >> simp []);
val _ = if null (hyp extract_oracle_some_suc_replay) then () else raise Fail "extract_oracle_some_suc hypotheses";
val _ = show_term "extract_oracle_some_suc_replay=" (concl extract_oracle_some_suc_replay);
val orac_agrees_s_rel_imp_replay = prove (
  ``source_evalProof$orac_agrees orac t.eval_state ==>
    source_evalProof$s_rel ci s t ==>
    i < FST (FST ((source_evalProof$orac_s t.eval_state).oracle 0)) ==>
    orac i = (source_evalProof$orac_s t.eval_state).oracle (i + 1)``,
  rw [source_evalProofTheory.s_rel_def, source_evalProofTheory.orac_agrees_def] >>
  fs [source_evalProofTheory.orac_s_def]);
val _ = if null (hyp orac_agrees_s_rel_imp_replay) then () else raise Fail "orac_agrees_s_rel_imp hypotheses";
val _ = show_term "orac_agrees_s_rel_imp_replay=" (concl orac_agrees_s_rel_imp_replay);
val recorded_orac_wf_defined_replay = prove (
  ``source_evalProof$recorded_orac_wf compiler orac /\
    i <= FST (FST (orac 0)) /\ 0 < i ==> compiler (orac i) <> NONE``,
  rw [source_evalProofTheory.recorded_orac_wf_def] >>
  Cases_on `i = FST (FST (orac 0))` >> fs [] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp [PULL_EXISTS]);
val _ = if null (hyp recorded_orac_wf_defined_replay) then () else raise Fail "recorded_orac_wf_defined hypotheses";
val _ = show_term "recorded_orac_wf_defined_replay=" (concl recorded_orac_wf_defined_replay);
val _ = show_term "is_insert_decs="
  ``source_evalProof$is_insert_oracle ci f (SOME (semanticPrimitives$EvalDecs eds))``;
val _ = show_term "declare_env_adjust="
  ``semanticPrimitives$declare_env (source_evalProof$adjust_oracle ci f es) env =
    (case semanticPrimitives$declare_env es env of NONE => NONE
     | SOME (x, es2) => SOME (x, source_evalProof$adjust_oracle ci f es2))``;
val _ = show_term "adjust_oracle_reset="
  ``source_evalProof$adjust_oracle ci f (semanticPrimitives$reset_env_generation es1 es2) =
    semanticPrimitives$reset_env_generation (source_evalProof$adjust_oracle ci f es1)
      (source_evalProof$adjust_oracle ci f es2)``;
val _ = show_term "is_insert_related="
  ``source_evalProof$is_insert_oracle ci f (SOME (semanticPrimitives$EvalOracle es)) ==>
    (es2.custom_do_eval = es.custom_do_eval /\ es2.oracle = es.oracle) ==>
    source_evalProof$is_insert_oracle ci f (SOME (semanticPrimitives$EvalOracle es2))``;
val _ = show_term "is_insert_reset="
  ``source_evalProof$is_insert_oracle ci f (semanticPrimitives$reset_env_generation es1 es2) =
    source_evalProof$is_insert_oracle ci f es2``;
val _ = show_term "declare_env_is_insert="
  ``semanticPrimitives$declare_env es env = SOME (x, es2) /\
    source_evalProof$is_insert_oracle ci f es ==> source_evalProof$is_insert_oracle ci f es2``;
val _ = show_term "do_eval_adjust="
  ``semanticPrimitives$do_eval vs es = SOME (env1, decs, es1) /\
    source_evalProof$is_insert_oracle ci f es ==>
    (semanticPrimitives$do_eval vs (source_evalProof$adjust_oracle ci (g o f) es) =
      SOME (env1, g decs, source_evalProof$adjust_oracle ci (g o f) es1) \/
     semanticPrimitives$do_eval vs (source_evalProof$adjust_oracle ci (g o f) es) =
      SOME (env1, decs, source_evalProof$adjust_oracle ci (g o f) es1)) /\
    source_evalProof$is_insert_oracle ci f es1``;

val declare_env_adjust_replay = prove (
  ``semanticPrimitives$declare_env (source_evalProof$adjust_oracle ci f es) env =
    (case semanticPrimitives$declare_env es env of NONE => NONE
     | SOME (x, es2) => SOME (x, source_evalProof$adjust_oracle ci f es2))``,
  simp [source_evalProofTheory.adjust_oracle_def, semanticPrimitivesTheory.declare_env_def] >>
  every_case_tac >> fs []);
val _ = if null (hyp declare_env_adjust_replay) then () else raise Fail "declare_env_adjust hypotheses";
val _ = show_term "declare_env_adjust_replay=" (concl declare_env_adjust_replay);

val adjust_oracle_reset_replay = prove (
  ``source_evalProof$adjust_oracle ci f (semanticPrimitives$reset_env_generation es1 es2) =
    semanticPrimitives$reset_env_generation (source_evalProof$adjust_oracle ci f es1)
      (source_evalProof$adjust_oracle ci f es2)``,
  simp [source_evalProofTheory.adjust_oracle_def, semanticPrimitivesTheory.reset_env_generation_def] >>
  every_case_tac >> fs []);
val _ = if null (hyp adjust_oracle_reset_replay) then () else raise Fail "adjust_oracle_reset hypotheses";
val _ = show_term "adjust_oracle_reset_replay=" (concl adjust_oracle_reset_replay);
