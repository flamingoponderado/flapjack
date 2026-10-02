load "preamble";
load "stack_removeProofTheory";
open bossLib HolKernel Parse preamble stack_removeProofTheory set_sepTheory;
val _ = Globals.linewidth := 20000;
val _ = print ("wr_def=" ^ term_to_string (concl word_list_rev_def) ^ "\n");
val _ = print ("wr_type=" ^ type_to_string (type_of ``stack_removeProof$word_list_rev``) ^ "\n");
fun check label q = let val th = prove(q,
  if label = "wr_wrong_address" then
    simp [word_list_rev_def,SEP_CLAUSES,one_def,pred_setTheory.EQUAL_SING,
      bytes_in_word_def,wordsTheory.dimindex_8] >> wordsLib.WORD_DECIDE_TAC
  else simp [word_list_rev_def,one_STAR,SEP_CLAUSES] >>
  CONV_TAC wordsLib.WORD_EVAL_CONV >>
  simp [one_def,emp_def,bytes_in_word_def,
    EXTENSION,FORALL_PROD,IN_DEF,wordsTheory.dimindex_1,wordsTheory.dimindex_8,
    wordsTheory.dimindex_32,wordsTheory.dimindex_64] >> (metis_tac [] ORELSE wordsLib.WORD_DECIDE_TAC))
  in print(label ^ "=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n") end;
val _ = check "wr_empty_generic" ``!address:'a word. word_list_rev address ([]:'b list) {}``;
val _ = check "wr_single_generic" ``!address:'a word value:'b. word_list_rev address [value] {(address-bytes_in_word,value)}``;
val _ = check "wr_wrap8" ``word_list_rev (0w:word8) [T] {(255w,T)}``;
val _ = check "wr_wrap32" ``word_list_rev (0w:word32) [7:num] {(n2w (2 EXP 32-4),7)}``;
val _ = check "wr_product64" ``word_list_rev (0w:word64) [(3:num,F)] {(n2w (2 EXP 64-8),(3,F))}``;
val _ = check "wr_wrap80" ``word_list_rev (0w:80 word) [F] {(n2w (2 EXP 80-10),F)}``;
val _ = check "wr_two64" ``word_list_rev (0w:word64) [T;F] {(n2w (2 EXP 64-8),T);(n2w (2 EXP 64-16),F)}``;
val _ = check "wr_zero_stride_distinct" ``word_list_rev (0w:word1) [T;F] {(0w,T);(0w,F)}``;
val _ = check "wr_zero_stride_same1" ``!heap. ~word_list_rev (0w:word1) [T;T] heap``;
val _ = check "wr_zero_stride_same7" ``!heap. ~word_list_rev (0w:7 word) [3:num;3] heap``;
val _ = check "wr_wrong_address" ``~word_list_rev (0w:word8) [T] {(0w,T)}``;
