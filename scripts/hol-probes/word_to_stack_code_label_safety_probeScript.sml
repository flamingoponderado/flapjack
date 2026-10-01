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
    val norm = REWRITE_CONV [stackPropsTheory.stack_good_code_labels_def, wordConvsTheory.good_code_labels_def,
      GSYM listTheory.LIST_TO_SET_MAP, finite_union] THENC EVAL THENC
      SIMP_CONV (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD,
        listTheory.LIST_TO_SET_THM, pred_setTheory.BIGUNION_INSERT,
        pred_setTheory.BIGUNION_EMPTY, stackPropsTheory.get_code_labels_def,
        stackPropsTheory.stack_get_handler_labels_def,
        wordConvsTheory.good_handlers_def, wordConvsTheory.get_code_labels_def, pred_setTheory.SUBSET_DEF] THENC EVAL;
    val th = prove(q, CONV_TAC norm THEN
      (SET_TAC [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] ORELSE
       (EXISTS_TAC ``8:num`` THEN EVAL_TAC)));
  in print (label ^ "="); print_term (rconc (EQT_INTRO th)); print "\n" end;

val _ = out "cls_empty" ``let p = []; e = {raise_stub_location;store_consts_stub_location}; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (T,T)``;
val _ = out "cls_self" ``let p = [(7,0,wordLang$LocValue 0 7)]; e = {raise_stub_location;store_consts_stub_location}; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (T,T)``;
val _ = out "cls_missing" ``let p = [(7,0,wordLang$LocValue 0 8)]; e = {raise_stub_location;store_consts_stub_location}; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (F,F)``;
val _ = out "cls_external" ``let p = [(7,0,wordLang$LocValue 99 8)]; e = {raise_stub_location;store_consts_stub_location;8}; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (T,T)``;
val _ = out "cls_duplicates" ``let p = [(7,0,wordLang$LocValue 0 7);(7,99,wordLang$LocValue 99 7)]; e = {raise_stub_location;store_consts_stub_location}; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (T,T)``;
val _ = out "cls_owned" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,7,5)))]; e = {raise_stub_location;store_consts_stub_location;8;9;10}; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (T,T)``;
val _ = out "cls_wrong_owner" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,9,5)))]; e = {raise_stub_location;store_consts_stub_location;8;9;10}; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (F,F)``;
val _ = out "cls_tail_missing" ``let p = [(7,0,wordLang$Call NONE (SOME 7) [] (SOME (0,wordLang$LocValue 0 8,999,5)))]; e = {raise_stub_location;store_consts_stub_location}; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (F,T)``;
val _ = out "cls_threaded" ``let p = [(7,5,wordLang$Alloc 0 (LN,LN));(8,0,wordLang$StoreConsts 0 0 0 0 [])]; e = {raise_stub_location;store_consts_stub_location}; (ps,fs,bm,i) = compile_word_to_stack (c:64 asm$asm_config) F 4 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (T,T)``;
val _ = out "cls_width_one" ``let p = [(7,0,wordLang$LocValue 99 8)]; e = UNIV; (ps,fs,bm,i) = compile_word_to_stack (c:1 asm$asm_config) F 0 p (Append (List [8w]) (List [2w]),5) in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e) = (T,T)``;
