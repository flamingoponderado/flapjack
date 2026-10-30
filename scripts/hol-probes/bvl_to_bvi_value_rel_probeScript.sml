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
