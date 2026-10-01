load "preamble";
load "word_to_stackTheory";
load "wordConvsTheory";
load "stackPropsTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory;
val finite_union = prove (``!ss. BIGUNION (set ss) = FOLDR $UNION {} ss``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [listTheory.FOLDR, listTheory.LIST_TO_SET_THM,
    pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY]);
(* Evaluate the actual compiler first, then discharge the resulting finite-set
   proposition in the original kernel. No compiler correctness theorem is used. *)
fun out label q =
  let
    val norm = REWRITE_CONV [stackPropsTheory.stack_good_handler_labels_def,
      GSYM listTheory.LIST_TO_SET_MAP, finite_union] THENC EVAL THENC
      SIMP_CONV (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD,
        listTheory.LIST_TO_SET_THM, pred_setTheory.BIGUNION_INSERT,
        pred_setTheory.BIGUNION_EMPTY, stackPropsTheory.get_code_labels_def,
        stackPropsTheory.stack_get_handler_labels_def,
        backendPropsTheory.restrict_nonzero_def, pred_setTheory.SUBSET_DEF] THENC EVAL;
    val th = prove(q, CONV_TAC norm THEN
      (SET_TAC [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] ORELSE
       (EXISTS_TAC ``9:num`` THEN EXISTS_TAC ``5:num`` THEN EVAL_TAC)));
  in print (label ^ "="); print_term (rconc (EQT_INTRO th)); print "\n" end;

val _ = out "hls_empty" ``let p = []; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (T,T)``;
val _ = out "hls_duplicates" ``let p = [(7,0,wordLang$LocValue 0 8);(7,0,wordLang$LocValue 99 9)]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (T,T)``;
val _ = out "hls_owned" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,7,5)))]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (T,T)``;
val _ = out "hls_wrong_owner" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,9,5)))]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (F,F)``;
val _ = out "hls_wrong_zero" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,9,0)))]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (F,T)``;
val _ = out "hls_wrong_one" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,9,1)));(9,0,wordLang$Skip)]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (F,T)``;
val _ = out "hls_tail_drop" ``let p = [(7,0,wordLang$Call NONE (SOME 8) [] (SOME (0,wordLang$LocValue 0 9,999,6)))]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (T,T)``;
val _ = out "hls_same_owner_twice" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,7,5)));(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,7,6)))]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (T,T)``;
val _ = out "hls_nested" ``let p = [(7,0,wordLang$Seq (wordLang$Loop LN (wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,7,5))) LN) (wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,7,6))))]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (T,T)``;
val _ = out "hls_nested_bad" ``let p = [(7,0,wordLang$Seq (wordLang$Loop LN (wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,9,5))) LN) (wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,7,6))))]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (F,F)``;
val _ = out "hls_threaded" ``let p = [(7,5,wordLang$Alloc 0 (LN,LN));(8,0,wordLang$StoreConsts 0 0 0 0 [])]; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (T,T)``;
val _ = out "hls_width_one" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,7,5)))]; (ps,fs,bm,i) = compile_word_to_stack (c:1 asm$asm_config) F 0 p (Append (List [8w]) (List [2w]),5) in (EVERY (\(n,m,pp).wordConvs$good_handlers n pp) p,stackProps$stack_good_handler_labels ps) = (T,T)``;
