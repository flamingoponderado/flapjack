load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory stackSemTheory arithmeticTheory listTheory rich_listTheory miscTheory;
val _ = Globals.linewidth := 4000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val IMP_filter_bitmap_EQ_SOME_NIL = prove(``!xs ys zs.
     (LENGTH xs = LENGTH ys) /\
     zs = MAP FST (FILTER SND (ZIP (ys, xs))) ==>
     (filter_bitmap xs ys = SOME (zs,[]))``,   Induct \\ Cases_on `ys` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def]);
val _ = (if null(hyp IMP_filter_bitmap_EQ_SOME_NIL) then () else raise Fail "open premise"; print "fb_full_IMP_filter_bitmap_EQ_SOME_NIL="; print_thm IMP_filter_bitmap_EQ_SOME_NIL; print "\n");
val filter_bitmap_length = prove(``∀bs ls xs ys.
  filter_bitmap bs ls = SOME(xs,ys) ⇒
  LENGTH xs ≤ LENGTH bs``,   ho_match_mp_tac filter_bitmap_ind>>fs[filter_bitmap_def]>>rw[]>>
  EVERY_CASE_TAC>>rveq>>fs[]>>res_tac>>
  rveq>>fs[]);
val _ = (if null(hyp filter_bitmap_length) then () else raise Fail "open premise"; print "fb_full_filter_bitmap_length="; print_thm filter_bitmap_length; print "\n");
val filter_bitmap_length_input = prove(``∀xs ys ls. filter_bitmap xs ys = SOME ls ⇒ LENGTH xs ≤ LENGTH ys``,   ho_match_mp_tac filter_bitmap_ind
  \\ simp[filter_bitmap_def,LENGTH_NIL_SYM]
  \\ rw[]
  \\ every_case_tac \\ fs[]);
val _ = (if null(hyp filter_bitmap_length_input) then () else raise Fail "open premise"; print "fb_full_filter_bitmap_length_input="; print_thm filter_bitmap_length_input; print "\n");
val filter_bitmap_MAP_IMP = prove(``∀ys xs l.
    filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[]) ∧
    filter_bitmap ys (MAP FST xs) = SOME (MAP FST l,[])
    ⇒
    filter_bitmap ys xs = SOME (l,[])``,   Induct \\ Cases_on`xs` \\ fs[filter_bitmap_def]
  \\ Cases \\ fs[filter_bitmap_def] \\ rpt strip_tac
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ Cases_on`l` \\ fs[]
  \\ rveq
  \\ first_x_assum drule
  \\ impl_tac >- metis_tac[]
  \\ simp[]
  \\ rw[]
  \\ metis_tac[PAIR]);
val _ = (if null(hyp filter_bitmap_MAP_IMP) then () else raise Fail "open premise"; print "fb_full_filter_bitmap_MAP_IMP="; print_thm filter_bitmap_MAP_IMP; print "\n");
val filter_bitmap_IMP_MAP_SND = prove(``!ys xs l.
     filter_bitmap ys xs = SOME (l,[]) ==>
     filter_bitmap ys (MAP SND xs) = SOME (MAP SND l,[])``,   Induct \\ Cases_on `xs` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ res_tac \\ fs []);
val _ = (if null(hyp filter_bitmap_IMP_MAP_SND) then () else raise Fail "open premise"; print "fb_full_filter_bitmap_IMP_MAP_SND="; print_thm filter_bitmap_IMP_MAP_SND; print "\n");
val filter_bitmap_IMP_MAP_FST = prove(``!ys xs l.
     filter_bitmap ys xs = SOME (l,[]) ==>
     filter_bitmap ys (MAP FST xs) = SOME (MAP FST l,[])``,   Induct \\ Cases_on `xs` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ res_tac \\ fs []);
val _ = (if null(hyp filter_bitmap_IMP_MAP_FST) then () else raise Fail "open premise"; print "fb_full_filter_bitmap_IMP_MAP_FST="; print_thm filter_bitmap_IMP_MAP_FST; print "\n");
val filter_bitmap_TAKE_LENGTH_IMP = prove(``!h5 x4 l.
     filter_bitmap h5 (TAKE (LENGTH h5) x4) = SOME (MAP SND l,[]) ==>
     filter_bitmap h5 x4 = SOME (MAP SND l,DROP (LENGTH h5) x4)``,   Induct \\ Cases_on `x4` \\ fs [filter_bitmap_def]
  \\ Cases \\ fs [filter_bitmap_def] \\ rpt strip_tac
  \\ EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ Cases_on `l` \\ fs [] \\ rw [] \\ res_tac \\ fs []);
val _ = (if null(hyp filter_bitmap_TAKE_LENGTH_IMP) then () else raise Fail "open premise"; print "fb_full_filter_bitmap_TAKE_LENGTH_IMP="; print_thm filter_bitmap_TAKE_LENGTH_IMP; print "\n");
val filter_bitmap_lemma = prove(``filter_bitmap h5 (index_list (TAKE (LENGTH h5) x4) k) = SOME (l,[]) ==>
   filter_bitmap h5 x4 = SOME (MAP SND l, DROP (LENGTH h5) x4)``,   rpt strip_tac \\ imp_res_tac filter_bitmap_IMP_MAP_SND
  \\ fs [MAP_SND_index_list] \\ imp_res_tac filter_bitmap_TAKE_LENGTH_IMP);
val _ = (if null(hyp filter_bitmap_lemma) then () else raise Fail "open premise"; print "fb_full_filter_bitmap_lemma="; print_thm filter_bitmap_lemma; print "\n");
val filter_bitmap_MEM = prove(``∀b ls ls' x.
  filter_bitmap b ls = SOME (ls',[]) ∧
  MEM x ls' ⇒ MEM x ls``,   ho_match_mp_tac filter_bitmap_ind>>
  rw[filter_bitmap_def]>>
  EVERY_CASE_TAC>>fs[]>>rveq>>
  fs[MEM]);
val _ = (if null(hyp filter_bitmap_MEM) then () else raise Fail "open premise"; print "fb_full_filter_bitmap_MEM="; print_thm filter_bitmap_MEM; print "\n");
fun emit label q = let val th = EVAL q in print(label ^ "="); print_thm th; print "\n" end;
val _ = emit "fb_output_0_0" ``filter_bitmap [] ([]:num list) = SOME (([]:num list),([]:num list))``;
val _ = emit "fb_pair_output_0_0" ``filter_bitmap [] ([]:(num # num) list) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_bounds_mem_0_0" ``LENGTH ([]:num list) <= LENGTH [] /\ LENGTH [] <= LENGTH ([]:num list) /\ EVERY (\x. MEM x ([]:num list)) ([]:num list)``;
val _ = emit "fb_index_0_0_0" ``filter_bitmap [] (index_list ([]:num list) 0) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_0_0_7" ``filter_bitmap [] (index_list ([]:num list) 7) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_0_1" ``filter_bitmap [] ([(3:num)]:num list) = SOME (([]:num list),([(3:num)]:num list))``;
val _ = emit "fb_pair_output_0_1" ``filter_bitmap [] ([((3:num),(96:num))]:(num # num) list) = SOME (([]:(num # num) list),([((3:num),(96:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_0_1" ``LENGTH ([]:num list) <= LENGTH [] /\ LENGTH [] <= LENGTH ([(3:num)]:num list) /\ EVERY (\x. MEM x ([(3:num)]:num list)) ([]:num list)``;
val _ = emit "fb_index_0_1_0" ``filter_bitmap [] (index_list ([]:num list) 0) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_0_1_7" ``filter_bitmap [] (index_list ([]:num list) 7) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_0_2" ``filter_bitmap [] ([(2:num);(5:num)]:num list) = SOME (([]:num list),([(2:num);(5:num)]:num list))``;
val _ = emit "fb_pair_output_0_2" ``filter_bitmap [] ([((2:num),(97:num));((5:num),(94:num))]:(num # num) list) = SOME (([]:(num # num) list),([((2:num),(97:num));((5:num),(94:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_0_2" ``LENGTH ([]:num list) <= LENGTH [] /\ LENGTH [] <= LENGTH ([(2:num);(5:num)]:num list) /\ EVERY (\x. MEM x ([(2:num);(5:num)]:num list)) ([]:num list)``;
val _ = emit "fb_index_0_2_0" ``filter_bitmap [] (index_list ([]:num list) 0) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_0_2_7" ``filter_bitmap [] (index_list ([]:num list) 7) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_0_3" ``filter_bitmap [] ([(8:num);(3:num);(6:num);(1:num)]:num list) = SOME (([]:num list),([(8:num);(3:num);(6:num);(1:num)]:num list))``;
val _ = emit "fb_pair_output_0_3" ``filter_bitmap [] ([((8:num),(91:num));((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list) = SOME (([]:(num # num) list),([((8:num),(91:num));((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_0_3" ``LENGTH ([]:num list) <= LENGTH [] /\ LENGTH [] <= LENGTH ([(8:num);(3:num);(6:num);(1:num)]:num list) /\ EVERY (\x. MEM x ([(8:num);(3:num);(6:num);(1:num)]:num list)) ([]:num list)``;
val _ = emit "fb_index_0_3_0" ``filter_bitmap [] (index_list ([]:num list) 0) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_0_3_7" ``filter_bitmap [] (index_list ([]:num list) 7) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_zip_reconstruct_0" ``filter_bitmap [] ([]:num list) = SOME (MAP FST (FILTER SND (ZIP (([]:num list),[]))),[])``;
val _ = emit "fb_output_1_0" ``filter_bitmap [F] ([]:num list) = NONE``;
val _ = emit "fb_pair_output_1_0" ``filter_bitmap [F] ([]:(num # num) list) = NONE``;
val _ = emit "fb_index_1_0_0" ``filter_bitmap [F] (index_list ([]:num list) 0) = NONE``;
val _ = emit "fb_index_1_0_7" ``filter_bitmap [F] (index_list ([]:num list) 7) = NONE``;
val _ = emit "fb_output_1_1" ``filter_bitmap [F] ([(3:num)]:num list) = SOME (([]:num list),([]:num list))``;
val _ = emit "fb_pair_output_1_1" ``filter_bitmap [F] ([((3:num),(96:num))]:(num # num) list) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_bounds_mem_1_1" ``LENGTH ([]:num list) <= LENGTH [F] /\ LENGTH [F] <= LENGTH ([(3:num)]:num list) /\ EVERY (\x. MEM x ([(3:num)]:num list)) ([]:num list)``;
val _ = emit "fb_index_1_1_0" ``filter_bitmap [F] (index_list ([(3:num)]:num list) 0) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_1_1_7" ``filter_bitmap [F] (index_list ([(3:num)]:num list) 7) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_1_2" ``filter_bitmap [F] ([(2:num);(5:num)]:num list) = SOME (([]:num list),([(5:num)]:num list))``;
val _ = emit "fb_pair_output_1_2" ``filter_bitmap [F] ([((2:num),(97:num));((5:num),(94:num))]:(num # num) list) = SOME (([]:(num # num) list),([((5:num),(94:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_1_2" ``LENGTH ([]:num list) <= LENGTH [F] /\ LENGTH [F] <= LENGTH ([(2:num);(5:num)]:num list) /\ EVERY (\x. MEM x ([(2:num);(5:num)]:num list)) ([]:num list)``;
val _ = emit "fb_index_1_2_0" ``filter_bitmap [F] (index_list ([(2:num)]:num list) 0) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_1_2_7" ``filter_bitmap [F] (index_list ([(2:num)]:num list) 7) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_1_3" ``filter_bitmap [F] ([(8:num);(3:num);(6:num);(1:num)]:num list) = SOME (([]:num list),([(3:num);(6:num);(1:num)]:num list))``;
val _ = emit "fb_pair_output_1_3" ``filter_bitmap [F] ([((8:num),(91:num));((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list) = SOME (([]:(num # num) list),([((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_1_3" ``LENGTH ([]:num list) <= LENGTH [F] /\ LENGTH [F] <= LENGTH ([(8:num);(3:num);(6:num);(1:num)]:num list) /\ EVERY (\x. MEM x ([(8:num);(3:num);(6:num);(1:num)]:num list)) ([]:num list)``;
val _ = emit "fb_index_1_3_0" ``filter_bitmap [F] (index_list ([(8:num)]:num list) 0) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_1_3_7" ``filter_bitmap [F] (index_list ([(8:num)]:num list) 7) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_zip_reconstruct_1" ``filter_bitmap [F] ([(0:num)]:num list) = SOME (MAP FST (FILTER SND (ZIP (([(0:num)]:num list),[F]))),[])``;
val _ = emit "fb_output_2_0" ``filter_bitmap [T] ([]:num list) = NONE``;
val _ = emit "fb_pair_output_2_0" ``filter_bitmap [T] ([]:(num # num) list) = NONE``;
val _ = emit "fb_index_2_0_0" ``filter_bitmap [T] (index_list ([]:num list) 0) = NONE``;
val _ = emit "fb_index_2_0_7" ``filter_bitmap [T] (index_list ([]:num list) 7) = NONE``;
val _ = emit "fb_output_2_1" ``filter_bitmap [T] ([(3:num)]:num list) = SOME (([(3:num)]:num list),([]:num list))``;
val _ = emit "fb_pair_output_2_1" ``filter_bitmap [T] ([((3:num),(96:num))]:(num # num) list) = SOME (([((3:num),(96:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_bounds_mem_2_1" ``LENGTH ([(3:num)]:num list) <= LENGTH [T] /\ LENGTH [T] <= LENGTH ([(3:num)]:num list) /\ EVERY (\x. MEM x ([(3:num)]:num list)) ([(3:num)]:num list)``;
val _ = emit "fb_index_2_1_0" ``filter_bitmap [T] (index_list ([(3:num)]:num list) 0) = SOME (([((0:num),(3:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_2_1_7" ``filter_bitmap [T] (index_list ([(3:num)]:num list) 7) = SOME (([((7:num),(3:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_2_2" ``filter_bitmap [T] ([(2:num);(5:num)]:num list) = SOME (([(2:num)]:num list),([(5:num)]:num list))``;
val _ = emit "fb_pair_output_2_2" ``filter_bitmap [T] ([((2:num),(97:num));((5:num),(94:num))]:(num # num) list) = SOME (([((2:num),(97:num))]:(num # num) list),([((5:num),(94:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_2_2" ``LENGTH ([(2:num)]:num list) <= LENGTH [T] /\ LENGTH [T] <= LENGTH ([(2:num);(5:num)]:num list) /\ EVERY (\x. MEM x ([(2:num);(5:num)]:num list)) ([(2:num)]:num list)``;
val _ = emit "fb_index_2_2_0" ``filter_bitmap [T] (index_list ([(2:num)]:num list) 0) = SOME (([((0:num),(2:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_2_2_7" ``filter_bitmap [T] (index_list ([(2:num)]:num list) 7) = SOME (([((7:num),(2:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_2_3" ``filter_bitmap [T] ([(8:num);(3:num);(6:num);(1:num)]:num list) = SOME (([(8:num)]:num list),([(3:num);(6:num);(1:num)]:num list))``;
val _ = emit "fb_pair_output_2_3" ``filter_bitmap [T] ([((8:num),(91:num));((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list) = SOME (([((8:num),(91:num))]:(num # num) list),([((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_2_3" ``LENGTH ([(8:num)]:num list) <= LENGTH [T] /\ LENGTH [T] <= LENGTH ([(8:num);(3:num);(6:num);(1:num)]:num list) /\ EVERY (\x. MEM x ([(8:num);(3:num);(6:num);(1:num)]:num list)) ([(8:num)]:num list)``;
val _ = emit "fb_index_2_3_0" ``filter_bitmap [T] (index_list ([(8:num)]:num list) 0) = SOME (([((0:num),(8:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_2_3_7" ``filter_bitmap [T] (index_list ([(8:num)]:num list) 7) = SOME (([((7:num),(8:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_zip_reconstruct_2" ``filter_bitmap [T] ([(0:num)]:num list) = SOME (MAP FST (FILTER SND (ZIP (([(0:num)]:num list),[T]))),[])``;
val _ = emit "fb_output_3_0" ``filter_bitmap [F;F] ([]:num list) = NONE``;
val _ = emit "fb_pair_output_3_0" ``filter_bitmap [F;F] ([]:(num # num) list) = NONE``;
val _ = emit "fb_index_3_0_0" ``filter_bitmap [F;F] (index_list ([]:num list) 0) = NONE``;
val _ = emit "fb_index_3_0_7" ``filter_bitmap [F;F] (index_list ([]:num list) 7) = NONE``;
val _ = emit "fb_output_3_1" ``filter_bitmap [F;F] ([(3:num)]:num list) = NONE``;
val _ = emit "fb_pair_output_3_1" ``filter_bitmap [F;F] ([((3:num),(96:num))]:(num # num) list) = NONE``;
val _ = emit "fb_index_3_1_0" ``filter_bitmap [F;F] (index_list ([(3:num)]:num list) 0) = NONE``;
val _ = emit "fb_index_3_1_7" ``filter_bitmap [F;F] (index_list ([(3:num)]:num list) 7) = NONE``;
val _ = emit "fb_output_3_2" ``filter_bitmap [F;F] ([(2:num);(5:num)]:num list) = SOME (([]:num list),([]:num list))``;
val _ = emit "fb_pair_output_3_2" ``filter_bitmap [F;F] ([((2:num),(97:num));((5:num),(94:num))]:(num # num) list) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_bounds_mem_3_2" ``LENGTH ([]:num list) <= LENGTH [F;F] /\ LENGTH [F;F] <= LENGTH ([(2:num);(5:num)]:num list) /\ EVERY (\x. MEM x ([(2:num);(5:num)]:num list)) ([]:num list)``;
val _ = emit "fb_index_3_2_0" ``filter_bitmap [F;F] (index_list ([(2:num);(5:num)]:num list) 0) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_3_2_7" ``filter_bitmap [F;F] (index_list ([(2:num);(5:num)]:num list) 7) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_3_3" ``filter_bitmap [F;F] ([(8:num);(3:num);(6:num);(1:num)]:num list) = SOME (([]:num list),([(6:num);(1:num)]:num list))``;
val _ = emit "fb_pair_output_3_3" ``filter_bitmap [F;F] ([((8:num),(91:num));((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list) = SOME (([]:(num # num) list),([((6:num),(93:num));((1:num),(98:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_3_3" ``LENGTH ([]:num list) <= LENGTH [F;F] /\ LENGTH [F;F] <= LENGTH ([(8:num);(3:num);(6:num);(1:num)]:num list) /\ EVERY (\x. MEM x ([(8:num);(3:num);(6:num);(1:num)]:num list)) ([]:num list)``;
val _ = emit "fb_index_3_3_0" ``filter_bitmap [F;F] (index_list ([(8:num);(3:num)]:num list) 0) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_3_3_7" ``filter_bitmap [F;F] (index_list ([(8:num);(3:num)]:num list) 7) = SOME (([]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_zip_reconstruct_3" ``filter_bitmap [F;F] ([(0:num);(1:num)]:num list) = SOME (MAP FST (FILTER SND (ZIP (([(0:num);(1:num)]:num list),[F;F]))),[])``;
val _ = emit "fb_output_4_0" ``filter_bitmap [T;F] ([]:num list) = NONE``;
val _ = emit "fb_pair_output_4_0" ``filter_bitmap [T;F] ([]:(num # num) list) = NONE``;
val _ = emit "fb_index_4_0_0" ``filter_bitmap [T;F] (index_list ([]:num list) 0) = NONE``;
val _ = emit "fb_index_4_0_7" ``filter_bitmap [T;F] (index_list ([]:num list) 7) = NONE``;
val _ = emit "fb_output_4_1" ``filter_bitmap [T;F] ([(3:num)]:num list) = NONE``;
val _ = emit "fb_pair_output_4_1" ``filter_bitmap [T;F] ([((3:num),(96:num))]:(num # num) list) = NONE``;
val _ = emit "fb_index_4_1_0" ``filter_bitmap [T;F] (index_list ([(3:num)]:num list) 0) = NONE``;
val _ = emit "fb_index_4_1_7" ``filter_bitmap [T;F] (index_list ([(3:num)]:num list) 7) = NONE``;
val _ = emit "fb_output_4_2" ``filter_bitmap [T;F] ([(2:num);(5:num)]:num list) = SOME (([(2:num)]:num list),([]:num list))``;
val _ = emit "fb_pair_output_4_2" ``filter_bitmap [T;F] ([((2:num),(97:num));((5:num),(94:num))]:(num # num) list) = SOME (([((2:num),(97:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_bounds_mem_4_2" ``LENGTH ([(2:num)]:num list) <= LENGTH [T;F] /\ LENGTH [T;F] <= LENGTH ([(2:num);(5:num)]:num list) /\ EVERY (\x. MEM x ([(2:num);(5:num)]:num list)) ([(2:num)]:num list)``;
val _ = emit "fb_index_4_2_0" ``filter_bitmap [T;F] (index_list ([(2:num);(5:num)]:num list) 0) = SOME (([((1:num),(2:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_4_2_7" ``filter_bitmap [T;F] (index_list ([(2:num);(5:num)]:num list) 7) = SOME (([((8:num),(2:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_4_3" ``filter_bitmap [T;F] ([(8:num);(3:num);(6:num);(1:num)]:num list) = SOME (([(8:num)]:num list),([(6:num);(1:num)]:num list))``;
val _ = emit "fb_pair_output_4_3" ``filter_bitmap [T;F] ([((8:num),(91:num));((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list) = SOME (([((8:num),(91:num))]:(num # num) list),([((6:num),(93:num));((1:num),(98:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_4_3" ``LENGTH ([(8:num)]:num list) <= LENGTH [T;F] /\ LENGTH [T;F] <= LENGTH ([(8:num);(3:num);(6:num);(1:num)]:num list) /\ EVERY (\x. MEM x ([(8:num);(3:num);(6:num);(1:num)]:num list)) ([(8:num)]:num list)``;
val _ = emit "fb_index_4_3_0" ``filter_bitmap [T;F] (index_list ([(8:num);(3:num)]:num list) 0) = SOME (([((1:num),(8:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_4_3_7" ``filter_bitmap [T;F] (index_list ([(8:num);(3:num)]:num list) 7) = SOME (([((8:num),(8:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_zip_reconstruct_4" ``filter_bitmap [T;F] ([(0:num);(1:num)]:num list) = SOME (MAP FST (FILTER SND (ZIP (([(0:num);(1:num)]:num list),[T;F]))),[])``;
val _ = emit "fb_output_5_0" ``filter_bitmap [F;T] ([]:num list) = NONE``;
val _ = emit "fb_pair_output_5_0" ``filter_bitmap [F;T] ([]:(num # num) list) = NONE``;
val _ = emit "fb_index_5_0_0" ``filter_bitmap [F;T] (index_list ([]:num list) 0) = NONE``;
val _ = emit "fb_index_5_0_7" ``filter_bitmap [F;T] (index_list ([]:num list) 7) = NONE``;
val _ = emit "fb_output_5_1" ``filter_bitmap [F;T] ([(3:num)]:num list) = NONE``;
val _ = emit "fb_pair_output_5_1" ``filter_bitmap [F;T] ([((3:num),(96:num))]:(num # num) list) = NONE``;
val _ = emit "fb_index_5_1_0" ``filter_bitmap [F;T] (index_list ([(3:num)]:num list) 0) = NONE``;
val _ = emit "fb_index_5_1_7" ``filter_bitmap [F;T] (index_list ([(3:num)]:num list) 7) = NONE``;
val _ = emit "fb_output_5_2" ``filter_bitmap [F;T] ([(2:num);(5:num)]:num list) = SOME (([(5:num)]:num list),([]:num list))``;
val _ = emit "fb_pair_output_5_2" ``filter_bitmap [F;T] ([((2:num),(97:num));((5:num),(94:num))]:(num # num) list) = SOME (([((5:num),(94:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_bounds_mem_5_2" ``LENGTH ([(5:num)]:num list) <= LENGTH [F;T] /\ LENGTH [F;T] <= LENGTH ([(2:num);(5:num)]:num list) /\ EVERY (\x. MEM x ([(2:num);(5:num)]:num list)) ([(5:num)]:num list)``;
val _ = emit "fb_index_5_2_0" ``filter_bitmap [F;T] (index_list ([(2:num);(5:num)]:num list) 0) = SOME (([((0:num),(5:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_5_2_7" ``filter_bitmap [F;T] (index_list ([(2:num);(5:num)]:num list) 7) = SOME (([((7:num),(5:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_5_3" ``filter_bitmap [F;T] ([(8:num);(3:num);(6:num);(1:num)]:num list) = SOME (([(3:num)]:num list),([(6:num);(1:num)]:num list))``;
val _ = emit "fb_pair_output_5_3" ``filter_bitmap [F;T] ([((8:num),(91:num));((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list) = SOME (([((3:num),(96:num))]:(num # num) list),([((6:num),(93:num));((1:num),(98:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_5_3" ``LENGTH ([(3:num)]:num list) <= LENGTH [F;T] /\ LENGTH [F;T] <= LENGTH ([(8:num);(3:num);(6:num);(1:num)]:num list) /\ EVERY (\x. MEM x ([(8:num);(3:num);(6:num);(1:num)]:num list)) ([(3:num)]:num list)``;
val _ = emit "fb_index_5_3_0" ``filter_bitmap [F;T] (index_list ([(8:num);(3:num)]:num list) 0) = SOME (([((0:num),(3:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_5_3_7" ``filter_bitmap [F;T] (index_list ([(8:num);(3:num)]:num list) 7) = SOME (([((7:num),(3:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_zip_reconstruct_5" ``filter_bitmap [F;T] ([(0:num);(1:num)]:num list) = SOME (MAP FST (FILTER SND (ZIP (([(0:num);(1:num)]:num list),[F;T]))),[])``;
val _ = emit "fb_output_6_0" ``filter_bitmap [T;T] ([]:num list) = NONE``;
val _ = emit "fb_pair_output_6_0" ``filter_bitmap [T;T] ([]:(num # num) list) = NONE``;
val _ = emit "fb_index_6_0_0" ``filter_bitmap [T;T] (index_list ([]:num list) 0) = NONE``;
val _ = emit "fb_index_6_0_7" ``filter_bitmap [T;T] (index_list ([]:num list) 7) = NONE``;
val _ = emit "fb_output_6_1" ``filter_bitmap [T;T] ([(3:num)]:num list) = NONE``;
val _ = emit "fb_pair_output_6_1" ``filter_bitmap [T;T] ([((3:num),(96:num))]:(num # num) list) = NONE``;
val _ = emit "fb_index_6_1_0" ``filter_bitmap [T;T] (index_list ([(3:num)]:num list) 0) = NONE``;
val _ = emit "fb_index_6_1_7" ``filter_bitmap [T;T] (index_list ([(3:num)]:num list) 7) = NONE``;
val _ = emit "fb_output_6_2" ``filter_bitmap [T;T] ([(2:num);(5:num)]:num list) = SOME (([(2:num);(5:num)]:num list),([]:num list))``;
val _ = emit "fb_pair_output_6_2" ``filter_bitmap [T;T] ([((2:num),(97:num));((5:num),(94:num))]:(num # num) list) = SOME (([((2:num),(97:num));((5:num),(94:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_bounds_mem_6_2" ``LENGTH ([(2:num);(5:num)]:num list) <= LENGTH [T;T] /\ LENGTH [T;T] <= LENGTH ([(2:num);(5:num)]:num list) /\ EVERY (\x. MEM x ([(2:num);(5:num)]:num list)) ([(2:num);(5:num)]:num list)``;
val _ = emit "fb_index_6_2_0" ``filter_bitmap [T;T] (index_list ([(2:num);(5:num)]:num list) 0) = SOME (([((1:num),(2:num));((0:num),(5:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_6_2_7" ``filter_bitmap [T;T] (index_list ([(2:num);(5:num)]:num list) 7) = SOME (([((8:num),(2:num));((7:num),(5:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_output_6_3" ``filter_bitmap [T;T] ([(8:num);(3:num);(6:num);(1:num)]:num list) = SOME (([(8:num);(3:num)]:num list),([(6:num);(1:num)]:num list))``;
val _ = emit "fb_pair_output_6_3" ``filter_bitmap [T;T] ([((8:num),(91:num));((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list) = SOME (([((8:num),(91:num));((3:num),(96:num))]:(num # num) list),([((6:num),(93:num));((1:num),(98:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_6_3" ``LENGTH ([(8:num);(3:num)]:num list) <= LENGTH [T;T] /\ LENGTH [T;T] <= LENGTH ([(8:num);(3:num);(6:num);(1:num)]:num list) /\ EVERY (\x. MEM x ([(8:num);(3:num);(6:num);(1:num)]:num list)) ([(8:num);(3:num)]:num list)``;
val _ = emit "fb_index_6_3_0" ``filter_bitmap [T;T] (index_list ([(8:num);(3:num)]:num list) 0) = SOME (([((1:num),(8:num));((0:num),(3:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_6_3_7" ``filter_bitmap [T;T] (index_list ([(8:num);(3:num)]:num list) 7) = SOME (([((8:num),(8:num));((7:num),(3:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_zip_reconstruct_6" ``filter_bitmap [T;T] ([(0:num);(1:num)]:num list) = SOME (MAP FST (FILTER SND (ZIP (([(0:num);(1:num)]:num list),[T;T]))),[])``;
val _ = emit "fb_output_7_0" ``filter_bitmap [T;F;T] ([]:num list) = NONE``;
val _ = emit "fb_pair_output_7_0" ``filter_bitmap [T;F;T] ([]:(num # num) list) = NONE``;
val _ = emit "fb_index_7_0_0" ``filter_bitmap [T;F;T] (index_list ([]:num list) 0) = NONE``;
val _ = emit "fb_index_7_0_7" ``filter_bitmap [T;F;T] (index_list ([]:num list) 7) = NONE``;
val _ = emit "fb_output_7_1" ``filter_bitmap [T;F;T] ([(3:num)]:num list) = NONE``;
val _ = emit "fb_pair_output_7_1" ``filter_bitmap [T;F;T] ([((3:num),(96:num))]:(num # num) list) = NONE``;
val _ = emit "fb_index_7_1_0" ``filter_bitmap [T;F;T] (index_list ([(3:num)]:num list) 0) = NONE``;
val _ = emit "fb_index_7_1_7" ``filter_bitmap [T;F;T] (index_list ([(3:num)]:num list) 7) = NONE``;
val _ = emit "fb_output_7_2" ``filter_bitmap [T;F;T] ([(2:num);(5:num)]:num list) = NONE``;
val _ = emit "fb_pair_output_7_2" ``filter_bitmap [T;F;T] ([((2:num),(97:num));((5:num),(94:num))]:(num # num) list) = NONE``;
val _ = emit "fb_index_7_2_0" ``filter_bitmap [T;F;T] (index_list ([(2:num);(5:num)]:num list) 0) = NONE``;
val _ = emit "fb_index_7_2_7" ``filter_bitmap [T;F;T] (index_list ([(2:num);(5:num)]:num list) 7) = NONE``;
val _ = emit "fb_output_7_3" ``filter_bitmap [T;F;T] ([(8:num);(3:num);(6:num);(1:num)]:num list) = SOME (([(8:num);(6:num)]:num list),([(1:num)]:num list))``;
val _ = emit "fb_pair_output_7_3" ``filter_bitmap [T;F;T] ([((8:num),(91:num));((3:num),(96:num));((6:num),(93:num));((1:num),(98:num))]:(num # num) list) = SOME (([((8:num),(91:num));((6:num),(93:num))]:(num # num) list),([((1:num),(98:num))]:(num # num) list))``;
val _ = emit "fb_bounds_mem_7_3" ``LENGTH ([(8:num);(6:num)]:num list) <= LENGTH [T;F;T] /\ LENGTH [T;F;T] <= LENGTH ([(8:num);(3:num);(6:num);(1:num)]:num list) /\ EVERY (\x. MEM x ([(8:num);(3:num);(6:num);(1:num)]:num list)) ([(8:num);(6:num)]:num list)``;
val _ = emit "fb_index_7_3_0" ``filter_bitmap [T;F;T] (index_list ([(8:num);(3:num);(6:num)]:num list) 0) = SOME (([((2:num),(8:num));((0:num),(6:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_index_7_3_7" ``filter_bitmap [T;F;T] (index_list ([(8:num);(3:num);(6:num)]:num list) 7) = SOME (([((9:num),(8:num));((7:num),(6:num))]:(num # num) list),([]:(num # num) list))``;
val _ = emit "fb_zip_reconstruct_7" ``filter_bitmap [T;F;T] ([(0:num);(1:num);(2:num)]:num list) = SOME (MAP FST (FILTER SND (ZIP (([(0:num);(1:num);(2:num)]:num list),[T;F;T]))),[])``;
