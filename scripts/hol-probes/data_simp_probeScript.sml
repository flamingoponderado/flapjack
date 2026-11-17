(* Typed source definitions for the data-language sequence simplifier in
   cakeml/compiler/backend/data_simpScript.sml. *)
load "data_simpTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "pSeq_def_typed" data_simpTheory.pSeq_def;
val _ = show "simp_def_typed" data_simpTheory.simp_def;
load "data_simpProofTheory";
val _ = show "get_code_labels_simp_typed" data_simpProofTheory.get_code_labels_simp;
val _ = show "simp_correct_typed" data_simpProofTheory.simp_correct;

(* Replay the local original sequencing lemmas with their inferred types. *)
load "preamble";
open preamble data_simpTheory dataSemTheory dataPropsTheory;
val evaluate_Seq_Skip = prove (
  ``!c s. evaluate (Seq c Skip,s) = evaluate (c,s)``,
  fs [evaluate_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate (c,s)` \\ fs [] \\ SRW_TAC [] []);
val _ = show "evaluate_Seq_Skip_replay_typed" evaluate_Seq_Skip;
val evaluate_pSeq = prove (
  ``evaluate (pSeq c1 c2, s) = evaluate (Seq c1 c2, s)``,
  SRW_TAC [] [pSeq_def] \\ fs [evaluate_Seq_Skip]);
val _ = show "evaluate_pSeq_replay_typed" evaluate_pSeq;
val lam_skip_id = prove (
  ``(λ(res,s1). if res = NONE then evaluate (Skip,s1) else (res,s1)) x = x``,
  Cases_on `x` \\ Cases_on `q` \\ rw[evaluate_def]);
val _ = show "lam_skip_id_replay_typed" lam_skip_id;
val evaluate_simp = prove (
  ``!c1 s c2. evaluate (simp c1 c2,s) = evaluate (Seq c1 c2,s)``,
  recInduct evaluate_ind \\ reverse (REPEAT STRIP_TAC) THEN1
   (Cases_on `handler` \\ fs [simp_def,evaluate_pSeq]
    \\ Cases_on `x` \\ fs [simp_def,evaluate_pSeq]
    \\ fs [evaluate_def]
    \\ every_case_tac >> fs[evaluate_def,LET_THM]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `evaluate (r,set_var q a r'') = (hres,hst)`
    \\ Cases_on `hres` \\ gvs [])
  \\ fs [simp_def,evaluate_def,LET_DEF,evaluate_pSeq,evaluate_pSeq]
  \\ Cases_on `evaluate (c1,s)` \\ fs [lam_skip_id]
  \\ Cases_on `evaluate (c2,r)` \\ fs [lam_skip_id]
  \\ Cases_on `evaluate (c2,set_var n a r)` \\ fs [lam_skip_id]
  \\ rw[] >> every_case_tac \\ fs [evaluate_def,lam_skip_id] \\ fs []
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ every_case_tac >> fs[evaluate_def,lam_skip_id]);
val _ = show "evaluate_simp_replay_typed" evaluate_simp;
