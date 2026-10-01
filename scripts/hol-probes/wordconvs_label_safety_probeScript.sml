load "preamble";
load "wordConvsTheory";
open bossLib HolKernel Parse preamble wordConvsTheory;
val finite_union = prove (``!ss. BIGUNION (set ss) = FOLDR $UNION {} ss``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [listTheory.FOLDR,
    listTheory.LIST_TO_SET_THM, pred_setTheory.BIGUNION_INSERT,
    pred_setTheory.BIGUNION_EMPTY]);
fun out label q =
  let
    val norm = REWRITE_CONV [good_code_labels_def, finite_union] THENC EVAL THENC
      SIMP_CONV (srw_ss()) [listTheory.LIST_TO_SET_THM,
        get_code_labels_def, pred_setTheory.SUBSET_DEF] THENC EVAL;
    val th = prove(q, CONV_TAC norm THEN
      (SET_TAC [] ORELSE (EXISTS_TAC ``8:num`` THEN EVAL_TAC)));
  in print (label ^ "="); print_term (rconc (EQT_INTRO th)); print "\n" end;
val _ = out "wcs_empty" ``good_code_labels ([] : (num # num # 64 wordLang$prog) list) {} = T``;
val _ = out "wcs_skip" ``good_code_labels ([(7,0,wordLang$Skip)] : (num # num # 64 wordLang$prog) list) {} = T``;
val _ = out "wcs_self" ``good_code_labels ([(7,0,wordLang$LocValue 0 7)] : (num # num # 64 wordLang$prog) list) {} = T``;
val _ = out "wcs_missing" ``good_code_labels ([(7,0,wordLang$LocValue 0 8)] : (num # num # 64 wordLang$prog) list) {} = F``;
val _ = out "wcs_external" ``good_code_labels ([(7,0,wordLang$LocValue 0 8)] : (num # num # 64 wordLang$prog) list) {8} = T``;
val _ = out "wcs_univ" ``good_code_labels ([(7,0,wordLang$LocValue 99 999)] : (num # num # 64 wordLang$prog) list) UNIV = T``;
val _ = out "wcs_duplicates" ``good_code_labels ([(7,0,wordLang$LocValue 0 7);(7,99,wordLang$LocValue 99 7)] : (num # num # 64 wordLang$prog) list) {} = T``;
val _ = out "wcs_cross" ``good_code_labels ([(7,0,wordLang$LocValue 0 8);(8,0,wordLang$LocValue 0 7)] : (num # num # 64 wordLang$prog) list) {} = T``;
val _ = out "wcs_owned" ``good_code_labels ([(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$Skip,11,12)) (SOME 7) [] (SOME (0,wordLang$LocValue 0 8,7,5)))] : (num # num # 64 wordLang$prog) list) {8} = T``;
val _ = out "wcs_wrong_owner" ``good_code_labels ([(7,0,wordLang$Call (SOME ([],(LN,LN),wordLang$Skip,11,12)) (SOME 7) [] (SOME (0,wordLang$LocValue 0 8,9,5)))] : (num # num # 64 wordLang$prog) list) {8} = F``;
val _ = out "wcs_tail_foreign" ``good_code_labels ([(7,0,wordLang$Call (NONE) (SOME 7) [] (SOME (0,wordLang$LocValue 0 8,999,5)))] : (num # num # 64 wordLang$prog) list) {8} = T``;
val _ = out "wcs_tail_missing" ``good_code_labels ([(7,0,wordLang$Call (NONE) (SOME 7) [] (SOME (0,wordLang$LocValue 0 8,999,5)))] : (num # num # 64 wordLang$prog) list) {} = F``;
val _ = out "wcs_nested" ``good_code_labels ([(7,0,wordLang$MustTerminate (wordLang$Seq (wordLang$Loop LN (wordLang$LocValue 0 7) LN) (wordLang$LocValue 0 8)))] : (num # num # 64 wordLang$prog) list) {8} = T``;
val _ = out "wcs_width_one" ``good_code_labels ([(7,0,wordLang$LocValue 99 8)] : (num # num # 1 wordLang$prog) list) {8} = T``;
