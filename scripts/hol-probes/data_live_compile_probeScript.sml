(* Typed source definitions for the data-language liveness pass in
   cakeml/compiler/backend/data_liveScript.sml. *)
load "data_liveTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "is_pure_def_typed" data_liveTheory.is_pure_def;
val _ = show "compile_def_typed" data_liveTheory.compile_def;
load "data_liveProofTheory";
val _ = show "get_code_labels_compile_typed" data_liveProofTheory.get_code_labels_compile;
val _ = show "compile_correct_typed" data_liveProofTheory.compile_correct;
val _ = show "state_rel_def_typed" data_liveProofTheory.state_rel_def;
(* Replay the local theorem with its source proof and inferred state types. *)
val state_rel_ID_replay = Q.prove (
  `!s live. data_liveProof$state_rel s s live`,
  simp [data_liveProofTheory.state_rel_def]);
val _ = show "state_rel_ID_replay_typed" state_rel_ID_replay;
(* The source induction theorem is local. Capture the exact inferred source
   statement; this quotation is typed evidence, not a replay of its proof. *)
val evaluate_compile_statement = Term `
  !c s1 res s2 l2 t1 l1 d.
    (dataSem$evaluate (c,s1) = (res,s2)) /\
    data_liveProof$state_rel s1 t1 l1 /\
    (data_live$compile c l2 = (d,l1)) /\
    (res <> SOME (Rerr (Rabort Rtype_error))) /\
    (!s3. (dataSem$jump_exc s1 = SOME s3) ==>
      ?t3. (dataSem$jump_exc t1 = SOME t3) /\
        data_liveProof$state_rel s3 t3 LN /\
        (t3.handler = s3.handler) /\ (LENGTH t3.stack = LENGTH s3.stack)) ==>
    ?t2. (dataSem$evaluate (d,t1) = (res,t2)) /\
      data_liveProof$state_rel s2 t2 (case res of NONE => l2 | _ => LN)`;
val _ = (print "evaluate_compile_statement_typed="; print_term evaluate_compile_statement; print "\n");
(* The local theorem is not exported; replay the original proof with inferred types. *)
val domain_list_delete_replay = Q.prove (
  `!xs l. sptree$domain (backend_common$list_delete xs l) =
          sptree$domain l DIFF set xs`,
  rw [pred_setTheory.EXTENSION, sptreeTheory.domain_lookup, backend_commonTheory.lookup_list_delete]
  >> Cases_on `MEM x xs` >> fs []);
val _ = show "domain_list_delete_replay_typed" domain_list_delete_replay;
(* Local source statement with inferred types; the original proof is not replayed here. *)
val pure_do_app_Rval_statement = Term `
  data_live$is_pure op /\ dataSem$do_app op x s = Rval (q,r) ==>
    ?safe smax. r = s with <|safe_for_space := safe; stack_max := smax|>`;
val _ = (print "is_pure_do_app_Rval_statement_typed=";
  print_term pure_do_app_Rval_statement; print "\n");

load "preamble";
open preamble data_liveTheory dataSemTheory dataLangTheory data_spaceTheory;
fun cases_on_op q = Cases_on q >|
  map (MAP_EVERY Cases_on) [[], [], [], [], [`b`], [`g`], [`m`], [], [`t`]];
val pure_do_app_Rval_replay = prove (
  ``is_pure op /\ do_app op x s = Rval (q,r) ==>
    ?safe smax. r = s with <|safe_for_space := safe; stack_max := smax|>``,
  cases_on_op `op` \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’)
  \\ dsimp[oneline is_pure_def,do_app_def,do_app_aux_def,AllCaseEqs(),AllCasePreds()]
  \\ simp[do_space_def,dataLangTheory.op_space_reset_def,
          data_spaceTheory.op_space_req_def,consume_space_def,do_install_def,UNCURRY,AllCaseEqs()]
  \\ rw[] \\ fs [state_component_equality,is_pure_def,dataLangTheory.op_space_reset_def,
                data_spaceTheory.op_space_req_def,allowed_op_def,do_stack_def,AllCaseEqs()]);
val _ = show "is_pure_do_app_Rval_replay_typed" pure_do_app_Rval_replay;

val pure_do_app_Rerr_replay = prove (
  ``is_pure op /\ do_app op xs s = Rerr e ==> Rabort Rtype_error = e``,
  cases_on_op `op` \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’)
  \\ fs [is_pure_def,do_app_def,do_app_aux_def]
  \\ simp[do_space_def,data_spaceTheory.op_space_req_def,
          case_eq_thms,do_install_def,UNCURRY] \\ rw[]);
val _ = show "is_pure_do_app_Rerr_replay_typed" pure_do_app_Rerr_replay;
