load "bossLib"; load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory;
fun print_eval label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = print_eval "al_base" ``OPTION_MAP LENGTH (abs_stack ([3w]:8 word list) ([]:8 wordSem$stack_frame list) [wordLang$Word 0w] []) = SOME 0``;
val _ = print_eval "al_plain" ``OPTION_MAP LENGTH (abs_stack ([3w]:8 word list) [wordSem$StackFrame NONE [] [] NONE :8 wordSem$stack_frame] [wordLang$Word 1w;wordLang$Word 7w;wordLang$Word 0w] [1]) = SOME 1``;
val _ = print_eval "al_handler" ``OPTION_MAP LENGTH (abs_stack ([3w]:8 word list) [wordSem$StackFrame NONE [] [] (SOME(0,1,2)) :8 wordSem$stack_frame] [wordLang$Word 1w;wordLang$Loc 1 2;wordLang$Word 6w;wordLang$Word 1w;wordLang$Word 7w;wordLang$Word 0w] [1]) = SOME 1``;
val _ = print_eval "al_nested" ``OPTION_MAP LENGTH (abs_stack ([3w]:8 word list) [wordSem$StackFrame NONE [] [] NONE :8 wordSem$stack_frame;wordSem$StackFrame NONE [] [] NONE] [wordLang$Word 1w;wordLang$Word 7w;wordLang$Word 1w;wordLang$Word 8w;wordLang$Word 0w] [1;1]) = SOME 2``;
val _ = print_eval "al_mixed" ``OPTION_MAP LENGTH (abs_stack ([3w]:8 word list) [wordSem$StackFrame NONE [] [] (SOME(0,1,2)) :8 wordSem$stack_frame;wordSem$StackFrame NONE [] [] NONE] [wordLang$Word 1w;wordLang$Loc 1 2;wordLang$Word 6w;wordLang$Word 1w;wordLang$Word 7w;wordLang$Word 1w;wordLang$Word 8w;wordLang$Word 0w] [1;1]) = SOME 2``;
