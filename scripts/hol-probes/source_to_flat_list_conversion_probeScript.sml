load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib source_to_flatProofTheory;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val _ = Globals.linewidth := 1000000;
val local_eqns =
  [``v_rel genv (Litv l) v``, ``v_rel genv (Conv cn vs) v``,
   ``v_rel genv (Loc b l) v``, ``v_rel genv (Vectorv vs) v``,
   ``env_rel genv nsEmpty env'``, ``env_rel genv (nsBind x v env) env'``,
   ``v_rel genv (Env e id) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> map GEN_ALL |> LIST_CONJ;
val chars_thm = prove(
  ``!genv. genv_c_ok genv.c ⇒ !v1 v2 vs1.
    v_rel genv v1 v2 ∧ semanticPrimitives$v_to_char_list v1 = SOME vs1 ⇒
    flatSem$v_to_char_list v2 = SOME vs1``,
  ntac 2 strip_tac >>
  ho_match_mp_tac semanticPrimitivesTheory.v_to_char_list_ind >>
  srw_tac[][semanticPrimitivesTheory.v_to_char_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_more_eqns, flatSemTheory.v_to_char_list_def] >>
  imp_res_tac genv_lookup_nil >> imp_res_tac genv_lookup_cons >>
  fs [] >> rw [flatSemTheory.v_to_char_list_def]);
val list_thm = prove(
  ``!genv. genv_c_ok genv.c ⇒ !v1 v2 vs1.
    v_rel genv v1 v2 ∧ semanticPrimitives$v_to_list v1 = SOME vs1 ⇒
    ?vs2. flatSem$v_to_list v2 = SOME vs2 ∧ LIST_REL (v_rel genv) vs1 vs2``,
  ntac 2 strip_tac >>
  ho_match_mp_tac semanticPrimitivesTheory.v_to_list_ind >>
  srw_tac[][semanticPrimitivesTheory.v_to_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[local_eqns, flatSemTheory.v_to_list_def] >>
  srw_tac[][] >> imp_res_tac genv_lookup_nil >> imp_res_tac genv_lookup_cons >>
  fs [] >> rw [flatSemTheory.v_to_list_def] >> res_tac >> fs []);
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "v_to_char_list_typed=" chars_thm;
val _ = show_thm "v_to_list_typed=" list_thm;
