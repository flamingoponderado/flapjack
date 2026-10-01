(* Original native helper observations; no translated evaluator. *)
load "preamble";
load "word_to_stackProofTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory stackPropsTheory;
fun out label q = (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");
fun original name goal =
  let val th = PART_MATCH (snd o strip_imp) (DB.fetch "word_to_stackProof" name) goal
      val result = if is_imp (concl th) then
        MATCH_MP th (prove (fst (dest_imp (concl th)), simp [no_install_def])) else th
      val _ = if null (hyp result) andalso aconv (concl result) goal then ()
              else raise Fail "original theorem application mismatch"
  in result end;
fun applied label name goal =
  (original name goal; out label goal);
val _ = applied "ni_moves_empty" "wMoveAux_no_install_lem"
  ``no_install (wMoveAux [] (0,0,0) : 64 stackLang$prog)``;
val _ = applied "ni_moves_all_pairs" "wMoveAux_no_install_lem"
  ``no_install (wMoveAux [(INL 1,INL 2);(INL 1,INR 2);(INR 1,INL 2);(INR 1,INR 2)] (0,0,0) : 1 stackLang$prog)``;
val _ = applied "ni_load_install" "wStackLoad_no_install_lem"
  ``no_install (wStackLoad [(9,0);(0,99)] (Install 0 1 2 3 4:64 stackLang$prog)) = no_install (Install 0 1 2 3 4:64 stackLang$prog)``;
val _ = applied "ni_load_skip" "wStackLoad_no_install_lem"
  ``no_install (wStackLoad [] (Skip:1 stackLang$prog)) = no_install (Skip:1 stackLang$prog)``;
val _ = applied "ni_reg1_direct" "wRegWrite1_no_install_lem"
  ``no_install (wRegWrite1 (\r. Inst (Const r 7w)) 2 (3,0,9):64 stackLang$prog)``;
val _ = applied "ni_reg1_spill" "wRegWrite1_no_install_lem"
  ``no_install (wRegWrite1 (\r. Inst (Const r 7w)) 99 (0,0,9):1 stackLang$prog)``;
val _ = applied "ni_reg2_direct" "wRegWrite2_no_install_lem"
  ``no_install (wRegWrite2 (\r. Inst (Const r 7w)) 2 (3,0,9):64 stackLang$prog)``;
val _ = applied "ni_reg2_spill" "wRegWrite2_no_install_lem"
  ``no_install (wRegWrite2 (\r. Inst (Const r 7w)) 99 (0,0,9):1 stackLang$prog)``;
val _ = applied "ni_live_zero" "wLive_no_install_lem"
  ``no_install (FST (wLive (LN,LN) (Nil,99) (0,0,17)):64 stackLang$prog)``;
val _ = applied "ni_live_frame" "wLive_no_install_lem"
  ``no_install (FST (wLive (LN,LN) (List [8w;2w],99) (4,7,3)):1 stackLang$prog)``;
val _ = applied "ni_stack_move_install" "stack_move_no_install_lem"
  ``no_install (stack_move 4 2 7 99 (Install 0 1 2 3 4:64 stackLang$prog)) = no_install (Install 0 1 2 3 4:64 stackLang$prog)``;
val _ = applied "ni_stack_move_zero" "stack_move_no_install_lem"
  ``no_install (stack_move 0 99 0 7 (Skip:1 stackLang$prog)) = no_install (Skip:1 stackLang$prog)``;
(* copy_ret_aux_no_install is local, so evaluate its exact source instance. *)
val _ = out "ni_copy_aux_zero" ``no_install (copy_ret_aux 0 99 0:64 stackLang$prog)``;
val _ = out "ni_copy_aux_many" ``no_install (copy_ret_aux 99 0 4:1 stackLang$prog)``;
