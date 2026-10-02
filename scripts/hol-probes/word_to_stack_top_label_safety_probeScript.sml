load "preamble"; load "word_to_stackProofTheory"; load "wordConvsTheory"; load "stackPropsTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory wordConvsTheory stackPropsTheory backendPropsTheory;
val _ = Globals.linewidth := 1000000;
fun theoremRow label th = let val th=GEN_ALL th in if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem"; print(label ^ "="); print_thm th; print "\n" end;
val word_to_stack_good_code_labels = prove(``compile asm_conf F progs = (bytes,bs,fs,prog') ∧
  good_code_labels progs elabs ⇒
  stack_good_code_labels prog' elabs``,   fs[word_to_stackTheory.compile_def]>>
  rpt(pairarg_tac>>fs[])>>
  fs[good_code_labels_def,stack_good_code_labels_def]>>
  rw[]>>
  old_drule compile_word_to_stack_code_labels>>
  disch_then $ qspecl_then [‘asm_conf’, ‘F’] mp_tac>>fs[]>>
  disch_then drule>>
  old_drule MAP_FST_compile_word_to_stack>>
  rw[]
  >- simp[raise_stub_F,store_consts_stub_def]
  >- simp[raise_stub_F,store_consts_stub_def]
  >>
  match_mp_tac SUBSET_TRANS>> asm_exists_tac>>simp[]>>
  rw[]
  >-
    (match_mp_tac IMAGE_SUBSET_gen>>
    asm_exists_tac>>simp[SUBSET_DEF]>>
    metis_tac[])
  >>
    fs[SUBSET_DEF]);
val _ = theoremRow "top_full_word_to_stack_good_code_labels" word_to_stack_good_code_labels;
val sub_union_lemma = prove(``x SUBSET y ==> x SUBSET y UNION z``,   fs [SUBSET_DEF]);
val word_to_stack_good_handler_labels = prove(``EVERY (λ(n,m,pp). good_handlers n pp) prog ⇒
  compile asm_conf F prog = (bytes,bs,fs,prog') ⇒
  stack_good_handler_labels prog'``,   fs[word_to_stackTheory.compile_def]>>
  rpt(pairarg_tac>>fs[])>>
  fs[stack_good_handler_labels_def]>>
  rw[]>>match_mp_tac sub_union_lemma>>
  old_drule compile_word_to_stack_code_labels>>
  disch_then $ qspecl_then [‘asm_conf’, ‘F’] mp_tac>>fs[]>>
  disch_then drule>>fs[]>>
  old_drule MAP_FST_compile_word_to_stack>>
  rw[]>>
  simp[raise_stub_F,store_consts_stub_def]>>
  old_drule backendPropsTheory.restrict_nonzero_SUBSET_left>>
  ONCE_REWRITE_TAC[INSERT_SING_UNION]>>
  ONCE_REWRITE_TAC[INSERT_SING_UNION]>>
  REWRITE_TAC[UNION_ASSOC]>>
  strip_tac>>
  old_drule backendPropsTheory.restrict_nonzero_left_union>>
  qmatch_goalsub_abbrev_tac`_ ⊆ restrict_nonzero xxx ∪ _`>>
  `restrict_nonzero xxx = {}` by
    (simp[backendPropsTheory.restrict_nonzero_def,Abbr`xxx`,EXTENSION,MEM_MAP]>>
    metis_tac[SND])>>
  simp[]);
val _ = theoremRow "top_full_word_to_stack_good_handler_labels" word_to_stack_good_handler_labels;
val finite_union = prove (``!ss. BIGUNION (set ss) = FOLDR $UNION {} ss``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [listTheory.FOLDR, listTheory.LIST_TO_SET_THM,
    pred_setTheory.BIGUNION_INSERT, pred_setTheory.BIGUNION_EMPTY]);
(* Evaluate the actual compiler first, then discharge the resulting finite-set
   proposition in the original kernel. No compiler correctness theorem is used. *)
fun out label q =
  let
    val norm = REWRITE_CONV [stackPropsTheory.stack_good_handler_labels_def, stackPropsTheory.stack_good_code_labels_def, wordConvsTheory.good_code_labels_def,
      GSYM listTheory.LIST_TO_SET_MAP, finite_union] THENC EVAL THENC
      SIMP_CONV (srw_ss()) [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD,
        listTheory.LIST_TO_SET_THM, pred_setTheory.BIGUNION_INSERT,
        pred_setTheory.BIGUNION_EMPTY, stackPropsTheory.get_code_labels_def,
        stackPropsTheory.stack_get_handler_labels_def,
        wordConvsTheory.good_handlers_def, wordConvsTheory.get_code_labels_def, pred_setTheory.SUBSET_DEF] THENC EVAL;
    val th = prove(q, CONV_TAC norm THEN
      (METIS_TAC [DECIDE ``(9:num) <> 5``, DECIDE ``(9:num) <> 6``, DECIDE ``(9:num) <> 7``, DECIDE ``(5:num) <> 0``, DECIDE ``(5:num) <> 1``] ORELSE SET_TAC [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] ORELSE
       (EXISTS_TAC ``8:num`` THEN EVAL_TAC)));
  in print (label ^ "="); print_term (rconc (EQT_INTRO th)); print "\n" end;

val _ = out "top_empty" ``let p = []; e = {}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (T,T,T)``;
val _ = out "top_self" ``let p = [(7,0,wordLang$LocValue 0 7)]; e = {}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (T,T,T)``;
val _ = out "top_missing" ``let p = [(7,0,wordLang$LocValue 0 8)]; e = {}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (F,F,T)``;
val _ = out "top_external" ``let p = [(7,0,wordLang$LocValue 99 8)]; e = {8}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (T,T,T)``;
val _ = out "top_duplicates" ``let p = [(7,0,wordLang$LocValue 0 7);(7,99,wordLang$LocValue 99 7)]; e = {}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (T,T,T)``;
val _ = out "top_owned" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,7,5)))]; e = {8;9;10}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (T,T,T)``;
val _ = out "top_wrong_owner" ``let p = [(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$LocValue 0 8,11,12)) (SOME 10) [] (SOME (0,wordLang$LocValue 0 9,9,5)))]; e = {8;9;10}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (F,F,F)``;
val _ = out "top_tail_missing" ``let p = [(7,0,wordLang$Call NONE (SOME 7) [] (SOME (0,wordLang$LocValue 0 8,999,5)))]; e = {}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (F,T,T)``;
val _ = out "top_threaded" ``let p = [(7,5,wordLang$Alloc 0 (LN,LN));(8,0,wordLang$StoreConsts 0 0 0 0 [])]; e = {}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (T,T,T)``;
val _ = out "top_width_one" ``let p = [(7,0,wordLang$LocValue 99 8)]; e = UNIV; (bm,bs,fs,ps) = compile ((c:1 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (T,T,T)``;
val _ = out "top_raise_owned" ``let p = [(7,0,wordLang$LocValue 0 raise_stub_location)]; e = {}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (F,T,T)``;
val _ = out "top_store_owned" ``let p = [(7,0,wordLang$LocValue 0 store_consts_stub_location)]; e = {}; (bm,bs,fs,ps) = compile ((c:64 asm$asm_config) with <|reg_count := 9; avoid_regs := []|>) F p in (wordConvs$good_code_labels p e,stackProps$stack_good_code_labels ps e,stackProps$stack_good_handler_labels ps) = (F,T,T)``;
