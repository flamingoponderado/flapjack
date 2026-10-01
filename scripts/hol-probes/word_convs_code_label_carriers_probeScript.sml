load "preamble";
load "wordConvsTheory";
open bossLib HolKernel Parse preamble;
fun out label q =
 let val th = prove(q, SIMP_TAC (srw_ss()) [wordConvsTheory.good_code_labels_def,
  wordConvsTheory.good_handlers_def, wordConvsTheory.get_code_labels_def,
  listTheory.LIST_TO_SET_THM, pred_setTheory.BIGUNION_INSERT,
  pred_setTheory.BIGUNION_EMPTY, pred_setTheory.SUBSET_DEF] THEN SET_TAC [])
 in print (label ^ "="); print_term (rconc (EQT_INTRO th)); print "\n" end;
val _ = out "clc_bool" ``wordConvs$good_code_labels ([(7,T,wordLang$LocValue 0 8)] : (num # bool # 64 wordLang$prog) list) {8} = T``;
val _ = out "clc_unit" ``wordConvs$good_code_labels ([(7,(),wordLang$LocValue 0 8)] : (num # unit # 64 wordLang$prog) list) {} = F``;
val _ = out "clc_list" ``wordConvs$good_code_labels ([(7,[T;F],wordLang$LocValue 99 7);(7,[],wordLang$Skip)] : (num # bool list # 1 wordLang$prog) list) {} = T``;
val _ = out "clc_option" ``wordConvs$good_code_labels ([(7,NONE:bool option,wordLang$LocValue 99 8)] : (num # bool option # 16 wordLang$prog) list) UNIV = T``;
