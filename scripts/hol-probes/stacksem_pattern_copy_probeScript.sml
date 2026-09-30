load "bossLib";
load "preamble";
load "stackSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory;
fun observe label q = let val th = EVAL q in
  (print (label ^ "="); print_term (rconc th); print "\n") end;
val _ = observe "zero" ``case stackSem$copy_words_for_pattern (0w:8 word) 0 10w 3w [7w;8w] UNIV (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "one_bypass" ``case stackSem$copy_words_for_pattern (1w:8 word) 9 10w 3w [] {} (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "even" ``case stackSem$copy_words_for_pattern (2w:8 word) 0 10w 3w [7w] UNIV (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "odd" ``case stackSem$copy_words_for_pattern (3w:8 word) 0 10w 3w [7w] UNIV (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "multi" ``case stackSem$copy_words_for_pattern (6w:8 word) 0 10w 3w [7w;8w] UNIV (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "missing_bitmap" ``case stackSem$copy_words_for_pattern (2w:8 word) 0 10w 3w [] UNIV (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "missing_domain" ``case stackSem$copy_words_for_pattern (2w:8 word) 0 10w 3w [7w] {} (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "later_domain" ``case stackSem$copy_words_for_pattern (4w:8 word) 0 10w 3w [7w;8w] {10w} (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "address_wrap" ``case stackSem$copy_words_for_pattern (6w:8 word) 0 255w 3w [7w;8w] UNIV (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 255w,m (255w+bytes_in_word),m 42w)``;
val _ = observe "value_wrap" ``case stackSem$copy_words_for_pattern (3w:8 word) 0 10w 250w [7w] UNIV (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "stride16" ``case stackSem$copy_words_for_pattern (6w:16 word) 0 10w 3w [7w;8w] UNIV (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
val _ = observe "stride4" ``case stackSem$copy_words_for_pattern (6w:4 word) 0 10w 3w [7w;8w] UNIV (K (Loc 9 9)) of NONE => NONE | SOME (j,b,m) => SOME (j,b,m 10w,m (10w+bytes_in_word),m 42w)``;
