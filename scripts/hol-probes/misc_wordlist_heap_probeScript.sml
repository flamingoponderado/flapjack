load "preamble";
load "miscTheory";
load "stack_removeTheory";
open bossLib HolKernel Parse preamble miscTheory set_sepTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("wl_def=" ^ term_to_string (concl word_list_def) ^ "\n");
val _ = print ("wl_type=" ^ type_to_string (type_of ``misc$word_list``) ^ "\n");
val _ = print ("we_def=" ^ term_to_string (concl word_list_exists_def) ^ "\n");
val _ = print ("we_type=" ^ type_to_string (type_of ``misc$word_list_exists``) ^ "\n");
fun check label q = let val th = prove(q,
  simp [word_list_def,one_STAR,SEP_CLAUSES] >>
  CONV_TAC wordsLib.WORD_EVAL_CONV >>
  simp [one_def,emp_def,bytes_in_word_def,EXTENSION,FORALL_PROD,IN_DEF,
    wordsTheory.dimindex_1,wordsTheory.dimindex_8,wordsTheory.dimindex_32,wordsTheory.dimindex_64] >>
  (metis_tac [] ORELSE wordsLib.WORD_DECIDE_TAC))
  in print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n") end;
fun checkExists label q = let val th = prove(q,
  rpt gen_tac >> simp [word_list_exists_def,SEP_EXISTS_THM,cond_STAR] >>
  (if label = "we_zero" then ALL_TAC
   else if label = "we_single" then qexists_tac `[x]`
   else if label = "we_wrap8" orelse label = "we_zero_distinct" then qexists_tac `[T;F]`
   else simp [listTheory.LENGTH_NIL,listTheory.LENGTH_EQ_1,PULL_EXISTS]) >>
  simp [word_list_def,one_STAR,SEP_CLAUSES] >>
  CONV_TAC wordsLib.WORD_EVAL_CONV >>
  simp [one_def,emp_def,bytes_in_word_def,pred_setTheory.EQUAL_SING,
    EXTENSION,FORALL_PROD,IN_DEF,wordsTheory.dimindex_1,wordsTheory.dimindex_8] >>
  (if label = "we_wrong_address" then
    rpt gen_tac >> qexists_tac `1w` >> qexists_tac `T` >> simp [] >> wordsLib.WORD_DECIDE_TAC
   else (metis_tac [] ORELSE wordsLib.WORD_DECIDE_TAC)))
  in print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n") end;
val _ = check "wl_empty" ``!a:'a word. word_list a ([]:'b list) {}``;
val _ = check "wl_single" ``!(a:'a word)(x:'b). word_list a [x] {(a,x)}``;
val _ = check "wl_wrap8" ``word_list (255w:word8) [T;F] {(255w,T);(0w,F)}``;
val _ = check "wl_wrap32" ``word_list (n2w (2 EXP 32-4):word32) [7:num;11] {(n2w (2 EXP 32-4),7);(0w,11)}``;
val _ = check "wl_product64" ``word_list (n2w (2 EXP 64-8):word64) [(3:num,F);(4,T)] {(n2w (2 EXP 64-8),(3,F));(0w,(4,T))}``;
val _ = check "wl_wrap80" ``word_list (n2w (2 EXP 80-10):80 word) [T;F] {(n2w (2 EXP 80-10),T);(0w,F)}``;
val _ = check "wl_zero_distinct" ``word_list (0w:word1) [T;F] {(0w,T);(0w,F)}``;
val _ = check "wl_zero_same1" ``!heap. ~word_list (0w:word1) [T;T] heap``;
val _ = check "wl_zero_same7" ``!heap. ~word_list (0w:7 word) [3:num;3] heap``;
val _ = checkExists "we_zero" ``!a:'a word. word_list_exists a 0 ({}:('a word#'b)set)``;
val _ = checkExists "we_single" ``!(a:'a word)(x:'b). word_list_exists a 1 {(a,x)}``;
val _ = checkExists "we_wrap8" ``word_list_exists (255w:word8) 2 {(255w,T);(0w,F)}``;
val _ = checkExists "we_zero_distinct" ``word_list_exists (0w:word1) 2 {(0w,T);(0w,F)}``;
val _ = checkExists "we_wrong_zero" ``~word_list_exists (0w:word8) 0 {(0w,T)}``;
val _ = checkExists "we_wrong_address" ``~word_list_exists (0w:word8) 1 {(1w,T)}``;
