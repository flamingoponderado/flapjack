(* Typed source statements for closure numbering correctness. *)
load "clos_numberProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "renumber_def_typed=" clos_numberTheory.renumber_code_locs_def;
val _ = show "compile_inc_def_typed=" clos_numberTheory.compile_inc_def;
val _ = show "make_even_def_typed=" miscTheory.make_even_def;
val _ = show "even_make_even_typed=" miscTheory.EVEN_make_even;
val _ = show "ignore_table_def_typed=" clos_numberTheory.ignore_table_def;
val _ = show "v_rel_rules_typed=" clos_numberProofTheory.v_rel_rules;
val _ = show "ref_rel_def_typed=" closPropsTheory.ref_rel_def;
val _ = show "fmap_rel_def_typed=" finite_mapTheory.fmap_rel_def;
val _ = show "state_rel_typed=" clos_numberProofTheory.state_rel_def;
val _ = show "renumber_correct_typed=" clos_numberProofTheory.renumber_code_locs_correct;
val _ = show "renumber_code_locs_inc_typed=" clos_numberProofTheory.renumber_code_locs_inc;
val _ = show "renumber_code_locs_imp_inc_typed=" clos_numberProofTheory.renumber_code_locs_imp_inc;
val _ = show "renumber_list_imp_length_typed=" clos_numberProofTheory.renumber_code_locs_list_IMP_LENGTH;
val _ = show "renumber_list_distinct_typed=" clos_numberProofTheory.renumber_code_locs_list_distinct;
val _ = show "renumber_even_typed=" clos_numberProofTheory.renumber_code_locs_EVEN;
val _ = show "renumber_code_locs_every_Fn_SOME_typed=" clos_numberProofTheory.renumber_code_locs_every_Fn_SOME;
open closLangTheory clos_numberTheory clos_numberProofTheory closSemTheory closPropsTheory
  listTheory rich_listTheory;
val dest_closure_v_rel_none_replay = Q.prove(
  `!f args f' args'.
    v_rel max_app f f' /\ LIST_REL (v_rel max_app) args args' /\
    dest_closure max_app NONE f args = NONE ==>
    dest_closure max_app NONE f' args' = NONE`,
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  full_simp_tac(srw_ss())[dest_closure_def, v_rel_cases] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[LET_THM, check_loc_def] >>
  srw_tac[][] >>
  imp_res_tac EVERY2_LENGTH >>
  srw_tac[][] >>
  TRY decide_tac >>
  Cases_on `EL k es` >>
  full_simp_tac(srw_ss())[] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[] >>
  Cases_on `renumber_code_locs_list n (MAP SND es)` >>
  imp_res_tac renumber_code_locs_list_length >>
  srw_tac[][] >>
  Cases_on `EL k (ZIP (MAP FST es,r'))` >>
  srw_tac[][] >>
  CCONTR_TAC >>
  full_simp_tac(srw_ss())[] >>
  `k < LENGTH es` by decide_tac >>
  `LENGTH (MAP FST es) = LENGTH r'` by metis_tac [LENGTH_MAP] >>
  full_simp_tac(srw_ss())[EL_ZIP, EL_MAP] >>
  srw_tac[][] >>
  rev_full_simp_tac(srw_ss())[]);
val _ = show "dest_closure_v_rel_none_replay_typed=" dest_closure_v_rel_none_replay;
val _ = show "semantics_number_typed=" clos_numberProofTheory.semantics_number;
