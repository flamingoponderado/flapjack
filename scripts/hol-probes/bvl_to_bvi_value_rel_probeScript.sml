load "bvl_to_bviProofTheory";
load "bviPropsTheory";
load "preamble";
open preamble bvl_to_bviProofTheory bvlSemTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "adjust_bv_def=" adjust_bv_def;
val _ = show "adjust_bv_Unit=" adjust_bv_Unit;
val _ = show "adjust_bv_Boolv=" adjust_bv_Boolv;
val _ = show "adjust_nested=" (EVAL ``adjust_bv (\n. n + 5)
  (Block 7 [Number ~3; RefPtr T 2; CodePtr 3; Block 8 [RefPtr F 9]])``);
val _ = show "aux_code_installed=" aux_code_installed_def;
val aux_code_installed_APPEND_replay = prove (``!xs ys code.
  aux_code_installed (xs ++ ys) code ==>
  aux_code_installed xs code /\ aux_code_installed ys code``,
  Induct \\ fs[APPEND,aux_code_installed_def,FORALL_PROD] \\ METIS_TAC []);
val _ = show "aux_code_installed_APPEND_replay=" aux_code_installed_APPEND_replay;
val _ = show "aux_code_installed_subspt=" aux_code_installed_subspt;
val _ = show "isVar_def=" bvlPropsTheory.isVar_def;
val _ = show "bVarBound_def=" bvlPropsTheory.bVarBound_def;
val _ = show "let_ok_def=" bvl_handleProofTheory.let_ok_def;
val _ = show "handle_ok_def=" bvl_handleProofTheory.handle_ok_def;
val _ = show "handle_ok_CONS=" bvl_handleProofTheory.handle_ok_CONS;
val _ = show "handle_ok_EVERY=" bvl_handleProofTheory.handle_ok_EVERY;
val _ = show "handle_good=" (prove (``bvl_handleProof$handle_ok
  [bvl$Let [] (bvl$Let [bvl$Var 0] (bvl$Var 0))]``,
  EVAL_TAC \\ simp[bvl_handleProofTheory.handle_ok_def]));
val _ = show "handle_bad=" (EVAL ``bvl_handleProof$handle_ok
  [bvl$Let [] (bvl$Let [bvl$Var 0] (bvl$Var 1))]``);
val _ = show "names_ok_def=" names_ok_def;
val _ = show "state_rel_def=" state_rel_def;
val _ = show "state_rel_FLOOKUP_byteArray=" state_rel_FLOOKUP_byteArray;
val _ = show "state_rel_FLOOKUP_valueArray=" state_rel_FLOOKUP_valueArray;
val _ = show "state_rel_FLOOKUP_MutBlock=" state_rel_FLOOKUP_MutBlock;
val _ = show "state_rel_FLOOKUP_Thunk=" state_rel_FLOOKUP_Thunk;
val _ = show "bv_ok_def=" bv_ok_def;
val _ = show "bv_ok_Unit=" bv_ok_Unit;
val _ = show "state_ok_def=" state_ok_def;
val _ = show "bvi_inc_clock_def=" bviPropsTheory.inc_clock_def;
val _ = show "bvi_inc_clock_ZERO=" bviPropsTheory.inc_clock_ZERO;
val _ = show "bvi_dec_clock_inv_clock1=" bviPropsTheory.dec_clock_inv_clock1;
val bv_ok_SUBSET_IMP_replay = prove (``!refs x refs2.
  bv_ok refs x /\ FDOM refs SUBSET FDOM refs2 ==> bv_ok refs2 x``,
  HO_MATCH_MP_TAC bv_ok_ind \\ full_simp_tac (srw_ss()) [bv_ok_def]
  \\ full_simp_tac (srw_ss()) [SUBSET_DEF,EVERY_MEM]);
val _ = show "bv_ok_SUBSET_IMP_replay=" bv_ok_SUBSET_IMP_replay;
val _ = show "list_to_v_ok=" list_to_v_ok;
val _ = show "list_to_v_ok_APPEND=" list_to_v_ok_APPEND;
val _ = show "do_app_refs_SUBSET=" bvlPropsTheory.do_app_refs_SUBSET;
val _ = show "evaluate_refs_SUBSET=" bvlPropsTheory.evaluate_refs_SUBSET;
val evaluate_IMP_bv_ok_replay = prove (``!xs env s res t a1 vs.
  bvlSem$evaluate (xs,env,s) = (res,t) ==>
  (bv_ok s.refs a1 ==> bv_ok t.refs a1) /\
  (EVERY (bv_ok s.refs) vs ==> EVERY (bv_ok t.refs) vs)``,
  REPEAT STRIP_TAC \\ full_simp_tac (srw_ss()) [EVERY_MEM]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC bvlPropsTheory.evaluate_refs_SUBSET \\ IMP_RES_TAC bv_ok_SUBSET_IMP_replay);
val _ = show "evaluate_IMP_bv_ok_replay=" evaluate_IMP_bv_ok_replay;
val _ = show "find_code_bv_ok=" find_code_bv_ok;
val _ = show "do_build_ok=" do_build_ok;
val _ = show "do_app_ok=" do_app_ok;
