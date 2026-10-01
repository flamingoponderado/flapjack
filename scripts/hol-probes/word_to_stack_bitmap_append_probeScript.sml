load "bossLib"; load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
fun print_eval label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = print_eval "ba_terminal" ``stackSem$read_bitmap ([13w]:8 word list) <> NONE /\ stackSem$read_bitmap ([13w] ++ [255w]:8 word list) = stackSem$read_bitmap ([13w]:8 word list)``;
val _ = print_eval "ba_continuation" ``stackSem$read_bitmap ([128w;3w]:8 word list) <> NONE /\ stackSem$read_bitmap ([128w;3w] ++ [255w]:8 word list) = stackSem$read_bitmap ([128w;3w]:8 word list)``;
val _ = print_eval "ba_full_one" ``stackSem$full_read_bitmap ([3w]:8 word list) (wordLang$Word 1w:8 wordLang$word_loc) <> NONE /\ stackSem$full_read_bitmap ([3w] ++ [255w]:8 word list) (wordLang$Word 1w:8 wordLang$word_loc) = stackSem$full_read_bitmap ([3w]:8 word list) (wordLang$Word 1w:8 wordLang$word_loc)``;
val _ = print_eval "ba_full_two" ``stackSem$full_read_bitmap ([0w;3w]:8 word list) (wordLang$Word 2w:8 wordLang$word_loc) <> NONE /\ stackSem$full_read_bitmap ([0w;3w] ++ [255w]:8 word list) (wordLang$Word 2w:8 wordLang$word_loc) = stackSem$full_read_bitmap ([0w;3w]:8 word list) (wordLang$Word 2w:8 wordLang$word_loc)``;
