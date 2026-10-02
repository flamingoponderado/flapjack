load "bossLib";
load "preamble";
load "stackPropsTheory";
open bossLib HolKernel Parse preamble stackPropsTheory stackSemTheory;
val _ = show_types := true;
fun capture label th = (print(label ^ "="); print_term(concl th); print "\n");
fun captureTypes label th = (print(label ^ "="); app (fn v =>
 print(term_to_string v ^ ":" ^ type_to_string(type_of v) ^ ";"))
 (fst(strip_forall(concl th)) @ free_vars(concl th)); print "\n");
val map_bitmap_length_source = prove (``∀a b c x y z.
  map_bitmap a b c = SOME(x,y,z) ⇒
  LENGTH c = LENGTH x + LENGTH z ∧
  LENGTH x = LENGTH a``,
  Induct>>rw[]>>
  Cases_on`b`>>TRY(Cases_on`h`)>>Cases_on`c`>>
  fs[map_bitmap_def]>>
  TRY(qpat_x_assum`A=x` (SUBST_ALL_TAC o SYM))>>
  TRY(qpat_x_assum`A=y` (SUBST_ALL_TAC o SYM))>>
  fs[LENGTH_NIL]>>
  pop_assum mp_tac>>every_case_tac>>rw[]>>res_tac>>
  fs[]>>DECIDE_TAC);
val _ = capture "map_bitmap_length" map_bitmap_length_source;
val _ = captureTypes "map_bitmap_length_types" map_bitmap_length_source;
val dec_stack_length_source = prove (``∀bs enc orig_stack new_stack.
  dec_stack bs enc orig_stack = SOME new_stack ⇒
  LENGTH orig_stack = LENGTH new_stack``,
  ho_match_mp_tac stackSemTheory.dec_stack_ind>>
  fs[stackSemTheory.dec_stack_def,LENGTH_NIL]>>rw[]>>
  pop_assum mp_tac>>
  Cases_on`w`>>fs[full_read_bitmap_def]>>
  every_case_tac>>fs[]>>
  rw[]>>
  imp_res_tac map_bitmap_length>>
  simp[]>>metis_tac[]);
val _ = capture "dec_stack_length" dec_stack_length_source;
val _ = captureTypes "dec_stack_length_types" dec_stack_length_source;
val _ = show_types := false;
fun observe label q = (print(label ^ "="); print_term(rconc(EVAL q)); print "\n");
val _ = observe "map_empty" ``stackSem$map_bitmap [] [10:num] [20;30]``;
val _ = observe "map_mixed" ``stackSem$map_bitmap [T;F;T] [10:num;11;12] [20;21;22;23]``;
val _ = observe "map_false" ``stackSem$map_bitmap [F;F] ([]:num list) [20;21;22]``;
val _ = observe "map_payload_lists" ``stackSem$map_bitmap [T;F] [[114:num];[117]] [[97];[98];[116]]``;
val _ = observe "map_missing_root" ``stackSem$map_bitmap [T] ([]:num list) [20]``;
val _ = observe "map_missing_value" ``stackSem$map_bitmap [F] [10:num] []``;
val _ = observe "dec_empty" ``stackSem$dec_stack ([]:word8 list) [] ([]:8 word_loc list)``;
val _ = observe "dec_zero" ``stackSem$dec_stack ([]:word8 list) [] ([Word 0w]:8 word_loc list)``;
val _ = observe "dec_true" ``stackSem$dec_stack ([3w]:word8 list) [Word 9w] ([Word 1w;Word 7w;Word 0w]:64 word_loc list)``;
val _ = observe "dec_false" ``stackSem$dec_stack ([2w]:word8 list) [] ([Word 1w;Loc 4 5;Word 0w]:64 word_loc list)``;
val _ = observe "dec_short_roots" ``stackSem$dec_stack ([3w]:word8 list) [] ([Word 1w;Word 7w;Word 0w]:64 word_loc list)``;
val _ = observe "dec_extra_roots" ``stackSem$dec_stack ([3w]:word8 list) [Word 9w;Word 10w] ([Word 1w;Word 7w;Word 0w]:64 word_loc list)``;
val _ = observe "dec_two" ``stackSem$dec_stack ([3w]:word8 list) [Word 9w;Loc 2 1] ([Word 1w;Word 7w;Word 1w;Loc 4 0;Word 0w]:80 word_loc list)``;
val _ = observe "dec_zero_extra" ``stackSem$dec_stack ([]:word8 list) [] ([Word 0w;Word 1w]:8 word_loc list)``;
val _ = observe "dec_mixed" ``stackSem$dec_stack ([3w]:word8 list) [Word 0w] ([Word 1w;Word 1w;Word 0w]:1 word_loc list)``;
val _ = observe "dec_narrow_bitmap" ``stackSem$dec_stack ([1w]:word1 list) [] ([Word 1w;Word 0w]:80 word_loc list)``;
val _ = observe "dec_loc_header" ``stackSem$dec_stack ([3w]:word8 list) [] ([Loc 1 0;Word 0w]:64 word_loc list)``;
val _ = observe "dec_missing_sentinel" ``stackSem$dec_stack ([3w]:word8 list) [Word 9w] ([Word 1w;Word 7w]:64 word_loc list)``;
