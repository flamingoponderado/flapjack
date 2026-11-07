load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib source_to_flatProofTheory;
val rveq = rpt BasicProvers.VAR_EQ_TAC;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val _ = Globals.linewidth := 1000000;

(* Replay the local do_eq theorem and proof from source_to_flatProofScript.sml. *)
val eq_thm = prove(
  ``∀genv. genv_c_ok genv.c ⇒
    (∀v1 v2 r v1_i1 v2_i1.
      semanticPrimitives$do_eq v1 v2 = r ∧ v_rel genv v1 v1_i1 ∧ v_rel genv v2 v2_i1 ⇒
      flatSem$do_eq v1_i1 v2_i1 = r) ∧
    (∀vs1 vs2 r vs1_i1 vs2_i1.
      semanticPrimitives$do_eq_list vs1 vs2 = r ∧ LIST_REL (v_rel genv) vs1 vs1_i1 ∧
      LIST_REL (v_rel genv) vs2 vs2_i1 ⇒ flatSem$do_eq_list vs1_i1 vs2_i1 = r)``,
  ntac 2 strip_tac >>
  ho_match_mp_tac semanticPrimitivesTheory.do_eq_ind >>
  rpt strip_tac >>
  fs [semanticPrimitivesTheory.Boolv_def, semanticPrimitivesTheory.do_eq_def,
      flatSemTheory.do_eq_def, v_rel_more_eqns] >>
  rveq >> fs [] >>
  rpt (irule COND_CONG >> rpt strip_tac) >>
  imp_res_tac listTheory.LIST_REL_LENGTH >>
  fs [flatSemTheory.ctor_same_type_def, semanticPrimitivesTheory.ctor_same_type_def] >>
  TRY every_case_tac >>
  gs [semanticPrimitivesTheory.lit_same_type_def] >>
  metis_tac [optionTheory.SOME_11, genv_c_ok_def
    |> SIMP_RULE (srw_ss()) [semanticPrimitivesTheory.ctor_same_type_def]]);
val _ = if null (hyp eq_thm) then () else raise Fail "unexpected equality theorem hypotheses";
val _ = (print "do_eq_typed=";
         Lib.with_flag (Globals.show_types,true) print_term (concl eq_thm));
