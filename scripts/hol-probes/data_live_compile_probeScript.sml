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
