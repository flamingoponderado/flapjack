(* Direct original StackSem309-354 codec observations for y19g.6.
   Read-only prebuilt oracle; full state/evaluator execution is not tested. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = print_eval "full_zero" ``stackSem$full_read_bitmap ([13w]:word8 list) (Word 0w : 8 word_loc)``;
val _ = print_eval "full_one" ``stackSem$full_read_bitmap ([13w]:word8 list) (Word 1w : 8 word_loc)``;
val _ = print_eval "full_two" ``stackSem$full_read_bitmap ([0w;5w]:word8 list) (Word 2w : 8 word_loc)``;
val _ = print_eval "full_oob" ``stackSem$full_read_bitmap ([13w]:word8 list) (Word 2w : 8 word_loc)``;
val _ = print_eval "full_loc" ``stackSem$full_read_bitmap ([13w]:word8 list) (Loc 1 0 : 8 word_loc)``;
val _ = print_eval "enc_empty" ``stackSem$enc_stack ([]:word8 list) ([] : 8 word_loc list)``;
val _ = print_eval "enc_zero" ``stackSem$enc_stack ([]:word8 list) ([Word 0w] : 8 word_loc list)``;
val _ = print_eval "enc_zero_extra" ``stackSem$enc_stack ([]:word8 list) ([Word 0w;Word 0w] : 8 word_loc list)``;
val _ = print_eval "enc_loc" ``stackSem$enc_stack ([3w]:word8 list) ([Loc 1 0;Word 0w] : 8 word_loc list)``;
val _ = print_eval "enc_true" ``stackSem$enc_stack ([3w]:word8 list) ([Word 1w;Word 7w;Word 0w] : 8 word_loc list)``;
val _ = print_eval "enc_false" ``stackSem$enc_stack ([2w]:word8 list) ([Word 1w;Loc 4 5;Word 0w] : 8 word_loc list)``;
val _ = print_eval "enc_two" ``stackSem$enc_stack ([3w]:word8 list) ([Word 1w;Word 7w;Word 1w;Loc 4 0;Word 0w] : 8 word_loc list)``;
val _ = print_eval "enc_short" ``stackSem$enc_stack ([3w]:word8 list) ([Word 1w] : 8 word_loc list)``;
val _ = print_eval "enc_missing_sentinel" ``stackSem$enc_stack ([3w]:word8 list) ([Word 1w;Word 7w] : 8 word_loc list)``;
val _ = print_eval "enc_bad_continuation" ``stackSem$enc_stack ([128w]:word8 list) ([Word 1w;Word 0w] : 8 word_loc list)``;
val _ = print_eval "dec_empty" ``stackSem$dec_stack ([]:word8 list) [] ([] : 8 word_loc list)``;
val _ = print_eval "dec_zero" ``stackSem$dec_stack ([]:word8 list) [] ([Word 0w] : 8 word_loc list)``;
val _ = print_eval "dec_true" ``stackSem$dec_stack ([3w]:word8 list) [Word 9w] ([Word 1w;Word 7w;Word 0w] : 8 word_loc list)``;
val _ = print_eval "dec_false" ``stackSem$dec_stack ([2w]:word8 list) [] ([Word 1w;Loc 4 5;Word 0w] : 8 word_loc list)``;
val _ = print_eval "dec_short_roots" ``stackSem$dec_stack ([3w]:word8 list) [] ([Word 1w;Word 7w;Word 0w] : 8 word_loc list)``;
val _ = print_eval "dec_extra_roots" ``stackSem$dec_stack ([3w]:word8 list) [Word 9w;Word 10w] ([Word 1w;Word 7w;Word 0w] : 8 word_loc list)``;
val _ = print_eval "dec_two" ``stackSem$dec_stack ([3w]:word8 list) [Word 9w;Loc 2 1] ([Word 1w;Word 7w;Word 1w;Loc 4 0;Word 0w] : 8 word_loc list)``;
val _ = print_eval "dec_zero_extra" ``stackSem$dec_stack ([]:word8 list) [] ([Word 0w;Word 1w] : 8 word_loc list)``;
val _ = print_eval "full_mixed" ``stackSem$full_read_bitmap ([13w]:word8 list) (Word 1w : 1 word_loc)``;
val _ = print_eval "enc_mixed" ``stackSem$enc_stack ([3w]:word8 list) ([Word 1w;Word 1w;Word 0w] : 1 word_loc list)``;
val _ = print_eval "dec_mixed" ``stackSem$dec_stack ([3w]:word8 list) [Word 0w] ([Word 1w;Word 1w;Word 0w] : 1 word_loc list)``;
val _ = (print "type_full="; print_type (type_of ``stackSem$full_read_bitmap``); print "\n");
val _ = (print "type_enc="; print_type (type_of ``stackSem$enc_stack``); print "\n");
val _ = (print "type_dec="; print_type (type_of ``stackSem$dec_stack``); print "\n");
