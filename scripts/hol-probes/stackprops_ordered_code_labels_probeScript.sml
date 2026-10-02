load "bossLib";
load "preamble";
load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackPropsTheory stackSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val find_code_labels_source = prove (``find_code d r code = SOME e ==>
    get_labels e SUBSET loc_check code``,
  Cases_on `d`
  \\ fs [stackSemTheory.find_code_def,SUBSET_DEF,IN_DEF,
         loc_check_def,FORALL_PROD]
  \\ every_case_tac \\ fs []
  \\ metis_tac []);
val _ = capture "extract_labels" (DB.fetch "stackProps" "extract_labels_def");
val _ = captureTypes "extract_labels_types" (DB.fetch "stackProps" "extract_labels_def");
val _ = capture "find_code_labels" find_code_labels_source;
val _ = captureTypes "find_code_labels_types" find_code_labels_source;
val _ = capture "find_code" (DB.fetch "stackSem" "find_code_def");
val _ = captureTypes "find_code_types" (DB.fetch "stackSem" "find_code_def");
val _ = capture "get_labels" (DB.fetch "stackSem" "get_labels_def");
val _ = captureTypes "get_labels_types" (DB.fetch "stackSem" "get_labels_def");
val _ = capture "loc_check" (DB.fetch "stackSem" "loc_check_def");
val _ = captureTypes "loc_check_types" (DB.fetch "stackSem" "loc_check_def");
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = observe "key_bool_direct" ``stackSem$find_code (INL 7 : num+bool) (FEMPTY : bool |-> 1 word_loc) (sptree$fromAList [(7,41:num)])``;
val _ = observe "key_bool_indirect" ``stackSem$find_code (INR T : num+bool) (FEMPTY |+ (T, Loc 7 0 : 1 word_loc)) (sptree$fromAList [(7,41:num)])``;
val _ = observe "key_bool_missing" ``stackSem$find_code (INR F : num+bool) (FEMPTY |+ (T, Loc 7 0 : 1 word_loc)) (sptree$fromAList [(7,41:num)])``;
val _ = observe "key_bool_nonzero" ``stackSem$find_code (INR T : num+bool) (FEMPTY |+ (T, Loc 7 2 : 1 word_loc)) (sptree$fromAList [(7,41:num)])``;
val _ = observe "key_bool_word" ``stackSem$find_code (INR T : num+bool) (FEMPTY |+ (T, Word 1w : 1 word_loc)) (sptree$fromAList [(7,41:num)])``;
val _ = observe "key_list_indirect" ``stackSem$find_code (INR [1;2] : num+num list) (FEMPTY |+ ([1;2], Loc 7 0 : 80 word_loc)) (sptree$fromAList [(7,41:num)])``;
val _ = observe "key_list_missing_code" ``stackSem$find_code (INR [1;2] : num+num list) (FEMPTY |+ ([1;2], Loc 8 0 : 80 word_loc)) (sptree$fromAList [(7,41:num)])``;
val _ = observe "key_nat_legacy" ``stackSem$find_code (INR 3 : num+num) (FEMPTY |+ (3, Loc 7 0 : 64 word_loc)) (sptree$fromAList [(7,41:num)])``;

val _ = observe "ordered_skip" ``extract_labels (Skip : 64 stackLang$prog)``;
val _ = observe "ordered_ignore_handler" ``extract_labels (Call NONE (INL 7) (SOME (Call (SOME (Skip,0,3,4)) (INL 8) NONE,1,2)) : 64 stackLang$prog)``;
val _ = observe "ordered_return" ``extract_labels (Call (SOME (Skip,9,1,2)) (INR 7) NONE : 64 stackLang$prog)``;
val _ = observe "ordered_both" ``extract_labels (Call (SOME (Skip,9,1,2)) (INL 7) (SOME (Skip,3,4)) : 64 stackLang$prog)``;
val _ = observe "ordered_nested" ``extract_labels (Call (SOME (Call (SOME (Skip,0,5,6)) (INL 0) NONE,9,1,2)) (INL 7) (SOME (Call (SOME (Skip,0,7,8)) (INL 0) NONE,3,4)) : 64 stackLang$prog)``;
val _ = observe "ordered_duplicate" ``extract_labels (Call (SOME (Call (SOME (Skip,0,1,2)) (INL 0) NONE,9,1,2)) (INL 7) (SOME (Skip,1,2)) : 1 stackLang$prog)``;
val _ = observe "ordered_sequence" ``extract_labels (Seq (Call (SOME (Skip,0,3,4)) (INL 0) NONE) (Call (SOME (Skip,0,1,2)) (INL 0) NONE) : 80 stackLang$prog)``;
val _ = observe "ordered_loop" ``extract_labels (Loop (Call (SOME (Skip,0,1,2)) (INL 0) NONE) : 64 stackLang$prog)``;
val _ = observe "ordered_if" ``extract_labels (If Equal 0 (Reg 1) (Call (SOME (Skip,0,3,4)) (INL 0) NONE) (Call (SOME (Skip,0,1,2)) (INL 0) NONE) : 64 stackLang$prog)``;
val _ = observe "ordered_leaf_labels" ``extract_labels (Seq (LocValue 0 1 2) (JumpLower 0 1 7) : 64 stackLang$prog)``;

val _ = capture "containment_bool_direct" (MATCH_MP find_code_labels_source (EVAL ``stackSem$find_code (INL 7 : num+bool) (FEMPTY : bool |-> 1 word_loc) (sptree$fromAList [(7,Call (SOME (Skip,0,1,2)) (INL 0) NONE : 80 stackLang$prog)])``));
val _ = capture "containment_list_indirect" (MATCH_MP find_code_labels_source (EVAL ``stackSem$find_code (INR [1;2] : num+num list) (FEMPTY |+ ([1;2],Loc 7 0 : 80 word_loc)) (sptree$fromAList [(7,Call (SOME (Skip,0,1,2)) (INL 0) NONE : 1 stackLang$prog)])``));
