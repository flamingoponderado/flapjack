(* Typed source definitions for the balanced switch construction in
   cakeml/compiler/backend/bvl_jumpScript.sml. *)
load "preamble";
load "bvl_jumpTheory";
load "bvl_jumpProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th = if null (hyp th) then
  (print (label ^ "="); print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");

val _ = show "JumpList_def_typed" bvl_jumpTheory.JumpList_def;
val _ = show "Jump_def_typed" bvl_jumpTheory.Jump_def;
val _ = show "evaluate_Jump_typed" bvl_jumpProofTheory.evaluate_Jump;
val _ = show "bvl_get_code_labels_JumpList_typed" bvl_jumpProofTheory.bvl_get_code_labels_JumpList;

(* The original evaluate_JumpList theorem is local; replay its source proof. *)
local
  open preamble bvl_jumpTheory bvlSemTheory bvlPropsTheory listTheory;
in
  val evaluate_JumpList_replay = Q.prove (
    `!n xs k.
       k < LENGTH xs ==>
       (evaluate ([JumpList n xs],Number (&(n+k))::env,s) =
        evaluate ([EL k xs],Number (&(n+k))::env,s))`,
    recInduct JumpList_ind \\ REPEAT STRIP_TAC \\ fs[]
    \\ SIMP_TAC std_ss [Once JumpList_def,LET_DEF]
    \\ fs [LENGTH_NIL]
    \\ IF_CASES_TAC THEN1 fs []
    \\ IF_CASES_TAC THEN1 fs []
    \\ fs [] \\ rw []
    \\ fs[bvlSemTheory.evaluate_def,do_app_def,do_int_app_def]
    \\ Q.ISPEC_THEN `xs` strip_assume_tac SPLIT_LIST
    \\ FULL_SIMP_TAC std_ss []
    \\ `(LENGTH ys = 0) ==> LENGTH zs <> 0` by (fs[] \\ DECIDE_TAC)
    \\ NTAC 2 (POP_ASSUM MP_TAC) \\ NTAC 4 (POP_ASSUM (K ALL_TAC))
    \\ REPEAT STRIP_TAC \\ fs[TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]
    \\ Cases_on `k < LENGTH ys` \\ fs[]
    \\ IMP_RES_TAC EL_APPEND1 \\ fs[]
    \\ `k - LENGTH ys < LENGTH zs` by DECIDE_TAC \\ RES_TAC
    \\ `n + LENGTH ys + (k - LENGTH ys) = n + k` by DECIDE_TAC
    \\ fs[] \\ fs[NOT_LESS]
    \\ IMP_RES_TAC EL_APPEND2 \\ fs [EL_APPEND2]);
  val _ = show "evaluate_JumpList_replay" evaluate_JumpList_replay;
end;
