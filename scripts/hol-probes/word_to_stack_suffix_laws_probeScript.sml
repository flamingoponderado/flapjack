load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory listTheory rich_listTheory arithmeticTheory miscTheory;
val _ = Globals.linewidth := 6000;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val LASTN_LENGTH_ID2 = prove(``  ∀stack x.
  (x+1 = LENGTH stack) ⇒
  LASTN (x+1) stack =
  HD stack::LASTN x stack``,   fs[LASTN_LENGTH_ID]>>Induct>>rw[]>>
  `x = LENGTH stack` by DECIDE_TAC>>
  fs[LASTN_CONS,LASTN_LENGTH_ID]);
val _ = (if null(hyp LASTN_LENGTH_ID2) then () else raise Fail "open premise"; print "sl_full_LASTN_LENGTH_ID2="; print_thm LASTN_LENGTH_ID2; print "\n");
val LASTN_LENGTH_BOUNDS = prove(``  ∀n ls.
  let xs = LASTN n ls in
  LENGTH xs ≤ n ∧
  LENGTH xs ≤ LENGTH ls``,   fs[LASTN_def,LET_THM]>>Induct>>fs[LENGTH_TAKE_EQ]);
val _ = (if null(hyp LASTN_LENGTH_BOUNDS) then () else raise Fail "open premise"; print "sl_full_LASTN_LENGTH_BOUNDS="; print_thm LASTN_LENGTH_BOUNDS; print "\n");
val LASTN_CONS_ID = prove(``  n = LENGTH ls ⇒
  LASTN (SUC n) (frame::ls) = (frame::ls)``,   rw[]>>EVAL_TAC>>fs[]);
val _ = (if null(hyp LASTN_CONS_ID) then () else raise Fail "open premise"; print "sl_full_LASTN_CONS_ID="; print_thm LASTN_CONS_ID; print "\n");
val LASTN_DROP2 = prove(``  ∀l n.
  LASTN n l = DROP (LENGTH l -n) l``,   Induct>>fs[LASTN_def]>>
  rw[TAKE_APPEND]>>
  Cases_on`n > LENGTH l`>>fs[ADD1]>>
  `LENGTH l - n = 0` by fs[]>>
  simp[DROP_def]);
val _ = (if null(hyp LASTN_DROP2) then () else raise Fail "open premise"; print "sl_full_LASTN_DROP2="; print_thm LASTN_DROP2; print "\n");
val EVERY_IMP_EVERY_LASTN = prove(``  !xs ys P. EVERY P xs /\ LASTN n xs = ys ==> EVERY P ys``,   fs [EVERY_MEM] \\ rw [] \\ imp_res_tac MEM_LASTN \\ res_tac);
val _ = (if null(hyp EVERY_IMP_EVERY_LASTN) then () else raise Fail "open premise"; print "sl_full_EVERY_IMP_EVERY_LASTN="; print_thm EVERY_IMP_EVERY_LASTN; print "\n");
val LASTN_LESS = prove(``  ∀ls n x xs.
  n+1 ≤ LENGTH ls ∧
  LASTN (n+1) ls = x::xs ⇒
  LASTN n ls = xs``,   Induct>>rw[]>>
  Cases_on`n+1 ≤ LENGTH ls`>>fs[]
  >-
    (fs[LASTN_CONS]>>
    res_tac>>fs[]>>
    `n ≤ LENGTH ls` by (fs[]>>decide_tac)>>
    fs[LASTN_CONS])
  >>
  `n = LENGTH ls` by DECIDE_TAC>>
  `n+1 = LENGTH (h::ls)` by (fs[]>>DECIDE_TAC)>>
  imp_res_tac LASTN_LENGTH_ID2>>
  fs[LASTN_CONS]);
val _ = (if null(hyp LASTN_LESS) then () else raise Fail "open premise"; print "sl_full_LASTN_LESS="; print_thm LASTN_LESS; print "\n");
(* Logical LASTN_def makes its total excess-index behavior evaluable. *)
fun emit label q = let val th = (REWRITE_CONV [LASTN_def] THENC EVAL) q in print(label ^ "="); print_thm th; print "\n" end;
val _ = emit "sl_suffix_Nat_0_0" ``(LASTN 0 ([]:num list),LENGTH(LASTN 0 ([]:num list)),LENGTH(LASTN 0 ([]:num list)) ≤ (0:num),LENGTH(LASTN 0 ([]:num list)) ≤ LENGTH ([]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 0 ([]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_0_0" ``(LASTN (0+1) ([]:num list),TL(LASTN (0+1) ([]:num list)),LASTN 0 ([]:num list),(0:num)+1 ≤ LENGTH ([]:num list)) = ([],[],[],F)``;
val _ = emit "sl_suffix_Nat_0_1" ``(LASTN 1 ([]:num list),LENGTH(LASTN 1 ([]:num list)),LENGTH(LASTN 1 ([]:num list)) ≤ (1:num),LENGTH(LASTN 1 ([]:num list)) ≤ LENGTH ([]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 1 ([]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_0_1" ``(LASTN (1+1) ([]:num list),TL(LASTN (1+1) ([]:num list)),LASTN 1 ([]:num list),(1:num)+1 ≤ LENGTH ([]:num list)) = ([],[],[],F)``;
val _ = emit "sl_suffix_Nat_0_2" ``(LASTN 2 ([]:num list),LENGTH(LASTN 2 ([]:num list)),LENGTH(LASTN 2 ([]:num list)) ≤ (2:num),LENGTH(LASTN 2 ([]:num list)) ≤ LENGTH ([]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 2 ([]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_0_2" ``(LASTN (2+1) ([]:num list),TL(LASTN (2+1) ([]:num list)),LASTN 2 ([]:num list),(2:num)+1 ≤ LENGTH ([]:num list)) = ([],[],[],F)``;
val _ = emit "sl_suffix_Nat_0_99" ``(LASTN 99 ([]:num list),LENGTH(LASTN 99 ([]:num list)),LENGTH(LASTN 99 ([]:num list)) ≤ (99:num),LENGTH(LASTN 99 ([]:num list)) ≤ LENGTH ([]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 99 ([]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_0_99" ``(LASTN (99+1) ([]:num list),TL(LASTN (99+1) ([]:num list)),LASTN 99 ([]:num list),(99:num)+1 ≤ LENGTH ([]:num list)) = ([],[],[],F)``;
val _ = emit "sl_suffix_Nat_0_900" ``(LASTN 900 ([]:num list),LENGTH(LASTN 900 ([]:num list)),LENGTH(LASTN 900 ([]:num list)) ≤ (900:num),LENGTH(LASTN 900 ([]:num list)) ≤ LENGTH ([]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 900 ([]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_0_900" ``(LASTN (900+1) ([]:num list),TL(LASTN (900+1) ([]:num list)),LASTN 900 ([]:num list),(900:num)+1 ≤ LENGTH ([]:num list)) = ([],[],[],F)``;
val _ = emit "sl_cons_Nat_0_0" ``LASTN (LENGTH ([]:num list)+1) (0::([]:num list)) = [0]``;
val _ = emit "sl_cons_Nat_0_99" ``LASTN (LENGTH ([]:num list)+1) (99::([]:num list)) = [99]``;
val _ = emit "sl_suffix_Nat_1_0" ``(LASTN 0 ([0]:num list),LENGTH(LASTN 0 ([0]:num list)),LENGTH(LASTN 0 ([0]:num list)) ≤ (0:num),LENGTH(LASTN 0 ([0]:num list)) ≤ LENGTH ([0]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 0 ([0]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_1_0" ``(LASTN (0+1) ([0]:num list),TL(LASTN (0+1) ([0]:num list)),LASTN 0 ([0]:num list),(0:num)+1 ≤ LENGTH ([0]:num list)) = ([0],[],[],T)``;
val _ = emit "sl_suffix_Nat_1_1" ``(LASTN 1 ([0]:num list),LENGTH(LASTN 1 ([0]:num list)),LENGTH(LASTN 1 ([0]:num list)) ≤ (1:num),LENGTH(LASTN 1 ([0]:num list)) ≤ LENGTH ([0]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 1 ([0]:num list))) = ([0],1,T,T,T)``;
val _ = emit "sl_less_Nat_1_1" ``(LASTN (1+1) ([0]:num list),TL(LASTN (1+1) ([0]:num list)),LASTN 1 ([0]:num list),(1:num)+1 ≤ LENGTH ([0]:num list)) = ([0],[],[0],F)``;
val _ = emit "sl_suffix_Nat_1_2" ``(LASTN 2 ([0]:num list),LENGTH(LASTN 2 ([0]:num list)),LENGTH(LASTN 2 ([0]:num list)) ≤ (2:num),LENGTH(LASTN 2 ([0]:num list)) ≤ LENGTH ([0]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 2 ([0]:num list))) = ([0],1,T,T,T)``;
val _ = emit "sl_less_Nat_1_2" ``(LASTN (2+1) ([0]:num list),TL(LASTN (2+1) ([0]:num list)),LASTN 2 ([0]:num list),(2:num)+1 ≤ LENGTH ([0]:num list)) = ([0],[],[0],F)``;
val _ = emit "sl_suffix_Nat_1_3" ``(LASTN 3 ([0]:num list),LENGTH(LASTN 3 ([0]:num list)),LENGTH(LASTN 3 ([0]:num list)) ≤ (3:num),LENGTH(LASTN 3 ([0]:num list)) ≤ LENGTH ([0]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 3 ([0]:num list))) = ([0],1,T,T,T)``;
val _ = emit "sl_less_Nat_1_3" ``(LASTN (3+1) ([0]:num list),TL(LASTN (3+1) ([0]:num list)),LASTN 3 ([0]:num list),(3:num)+1 ≤ LENGTH ([0]:num list)) = ([0],[],[0],F)``;
val _ = emit "sl_suffix_Nat_1_99" ``(LASTN 99 ([0]:num list),LENGTH(LASTN 99 ([0]:num list)),LENGTH(LASTN 99 ([0]:num list)) ≤ (99:num),LENGTH(LASTN 99 ([0]:num list)) ≤ LENGTH ([0]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 99 ([0]:num list))) = ([0],1,T,T,T)``;
val _ = emit "sl_less_Nat_1_99" ``(LASTN (99+1) ([0]:num list),TL(LASTN (99+1) ([0]:num list)),LASTN 99 ([0]:num list),(99:num)+1 ≤ LENGTH ([0]:num list)) = ([0],[],[0],F)``;
val _ = emit "sl_suffix_Nat_1_900" ``(LASTN 900 ([0]:num list),LENGTH(LASTN 900 ([0]:num list)),LENGTH(LASTN 900 ([0]:num list)) ≤ (900:num),LENGTH(LASTN 900 ([0]:num list)) ≤ LENGTH ([0]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 900 ([0]:num list))) = ([0],1,T,T,T)``;
val _ = emit "sl_less_Nat_1_900" ``(LASTN (900+1) ([0]:num list),TL(LASTN (900+1) ([0]:num list)),LASTN 900 ([0]:num list),(900:num)+1 ≤ LENGTH ([0]:num list)) = ([0],[],[0],F)``;
val _ = emit "sl_head_Nat_1" ``(LASTN (LENGTH ([0]:num list)) ([0]:num list), HD ([0]:num list)::LASTN (0) ([0]:num list)) = ([0],[0])``;
val _ = emit "sl_cons_Nat_1_0" ``LASTN (LENGTH ([0]:num list)+1) (0::([0]:num list)) = [0;0]``;
val _ = emit "sl_cons_Nat_1_99" ``LASTN (LENGTH ([0]:num list)+1) (99::([0]:num list)) = [99;0]``;
val _ = emit "sl_suffix_Nat_2_0" ``(LASTN 0 ([9]:num list),LENGTH(LASTN 0 ([9]:num list)),LENGTH(LASTN 0 ([9]:num list)) ≤ (0:num),LENGTH(LASTN 0 ([9]:num list)) ≤ LENGTH ([9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 0 ([9]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_2_0" ``(LASTN (0+1) ([9]:num list),TL(LASTN (0+1) ([9]:num list)),LASTN 0 ([9]:num list),(0:num)+1 ≤ LENGTH ([9]:num list)) = ([9],[],[],T)``;
val _ = emit "sl_suffix_Nat_2_1" ``(LASTN 1 ([9]:num list),LENGTH(LASTN 1 ([9]:num list)),LENGTH(LASTN 1 ([9]:num list)) ≤ (1:num),LENGTH(LASTN 1 ([9]:num list)) ≤ LENGTH ([9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 1 ([9]:num list))) = ([9],1,T,T,F)``;
val _ = emit "sl_less_Nat_2_1" ``(LASTN (1+1) ([9]:num list),TL(LASTN (1+1) ([9]:num list)),LASTN 1 ([9]:num list),(1:num)+1 ≤ LENGTH ([9]:num list)) = ([9],[],[9],F)``;
val _ = emit "sl_suffix_Nat_2_2" ``(LASTN 2 ([9]:num list),LENGTH(LASTN 2 ([9]:num list)),LENGTH(LASTN 2 ([9]:num list)) ≤ (2:num),LENGTH(LASTN 2 ([9]:num list)) ≤ LENGTH ([9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 2 ([9]:num list))) = ([9],1,T,T,F)``;
val _ = emit "sl_less_Nat_2_2" ``(LASTN (2+1) ([9]:num list),TL(LASTN (2+1) ([9]:num list)),LASTN 2 ([9]:num list),(2:num)+1 ≤ LENGTH ([9]:num list)) = ([9],[],[9],F)``;
val _ = emit "sl_suffix_Nat_2_3" ``(LASTN 3 ([9]:num list),LENGTH(LASTN 3 ([9]:num list)),LENGTH(LASTN 3 ([9]:num list)) ≤ (3:num),LENGTH(LASTN 3 ([9]:num list)) ≤ LENGTH ([9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 3 ([9]:num list))) = ([9],1,T,T,F)``;
val _ = emit "sl_less_Nat_2_3" ``(LASTN (3+1) ([9]:num list),TL(LASTN (3+1) ([9]:num list)),LASTN 3 ([9]:num list),(3:num)+1 ≤ LENGTH ([9]:num list)) = ([9],[],[9],F)``;
val _ = emit "sl_suffix_Nat_2_99" ``(LASTN 99 ([9]:num list),LENGTH(LASTN 99 ([9]:num list)),LENGTH(LASTN 99 ([9]:num list)) ≤ (99:num),LENGTH(LASTN 99 ([9]:num list)) ≤ LENGTH ([9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 99 ([9]:num list))) = ([9],1,T,T,F)``;
val _ = emit "sl_less_Nat_2_99" ``(LASTN (99+1) ([9]:num list),TL(LASTN (99+1) ([9]:num list)),LASTN 99 ([9]:num list),(99:num)+1 ≤ LENGTH ([9]:num list)) = ([9],[],[9],F)``;
val _ = emit "sl_suffix_Nat_2_900" ``(LASTN 900 ([9]:num list),LENGTH(LASTN 900 ([9]:num list)),LENGTH(LASTN 900 ([9]:num list)) ≤ (900:num),LENGTH(LASTN 900 ([9]:num list)) ≤ LENGTH ([9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 900 ([9]:num list))) = ([9],1,T,T,F)``;
val _ = emit "sl_less_Nat_2_900" ``(LASTN (900+1) ([9]:num list),TL(LASTN (900+1) ([9]:num list)),LASTN 900 ([9]:num list),(900:num)+1 ≤ LENGTH ([9]:num list)) = ([9],[],[9],F)``;
val _ = emit "sl_head_Nat_2" ``(LASTN (LENGTH ([9]:num list)) ([9]:num list), HD ([9]:num list)::LASTN (0) ([9]:num list)) = ([9],[9])``;
val _ = emit "sl_cons_Nat_2_0" ``LASTN (LENGTH ([9]:num list)+1) (0::([9]:num list)) = [0;9]``;
val _ = emit "sl_cons_Nat_2_99" ``LASTN (LENGTH ([9]:num list)+1) (99::([9]:num list)) = [99;9]``;
val _ = emit "sl_suffix_Nat_3_0" ``(LASTN 0 ([1;2]:num list),LENGTH(LASTN 0 ([1;2]:num list)),LENGTH(LASTN 0 ([1;2]:num list)) ≤ (0:num),LENGTH(LASTN 0 ([1;2]:num list)) ≤ LENGTH ([1;2]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 0 ([1;2]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_3_0" ``(LASTN (0+1) ([1;2]:num list),TL(LASTN (0+1) ([1;2]:num list)),LASTN 0 ([1;2]:num list),(0:num)+1 ≤ LENGTH ([1;2]:num list)) = ([2],[],[],T)``;
val _ = emit "sl_suffix_Nat_3_1" ``(LASTN 1 ([1;2]:num list),LENGTH(LASTN 1 ([1;2]:num list)),LENGTH(LASTN 1 ([1;2]:num list)) ≤ (1:num),LENGTH(LASTN 1 ([1;2]:num list)) ≤ LENGTH ([1;2]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 1 ([1;2]:num list))) = ([2],1,T,T,T)``;
val _ = emit "sl_less_Nat_3_1" ``(LASTN (1+1) ([1;2]:num list),TL(LASTN (1+1) ([1;2]:num list)),LASTN 1 ([1;2]:num list),(1:num)+1 ≤ LENGTH ([1;2]:num list)) = ([1;2],[2],[2],T)``;
val _ = emit "sl_suffix_Nat_3_2" ``(LASTN 2 ([1;2]:num list),LENGTH(LASTN 2 ([1;2]:num list)),LENGTH(LASTN 2 ([1;2]:num list)) ≤ (2:num),LENGTH(LASTN 2 ([1;2]:num list)) ≤ LENGTH ([1;2]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 2 ([1;2]:num list))) = ([1;2],2,T,T,F)``;
val _ = emit "sl_less_Nat_3_2" ``(LASTN (2+1) ([1;2]:num list),TL(LASTN (2+1) ([1;2]:num list)),LASTN 2 ([1;2]:num list),(2:num)+1 ≤ LENGTH ([1;2]:num list)) = ([1;2],[2],[1;2],F)``;
val _ = emit "sl_suffix_Nat_3_3" ``(LASTN 3 ([1;2]:num list),LENGTH(LASTN 3 ([1;2]:num list)),LENGTH(LASTN 3 ([1;2]:num list)) ≤ (3:num),LENGTH(LASTN 3 ([1;2]:num list)) ≤ LENGTH ([1;2]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 3 ([1;2]:num list))) = ([1;2],2,T,T,F)``;
val _ = emit "sl_less_Nat_3_3" ``(LASTN (3+1) ([1;2]:num list),TL(LASTN (3+1) ([1;2]:num list)),LASTN 3 ([1;2]:num list),(3:num)+1 ≤ LENGTH ([1;2]:num list)) = ([1;2],[2],[1;2],F)``;
val _ = emit "sl_suffix_Nat_3_4" ``(LASTN 4 ([1;2]:num list),LENGTH(LASTN 4 ([1;2]:num list)),LENGTH(LASTN 4 ([1;2]:num list)) ≤ (4:num),LENGTH(LASTN 4 ([1;2]:num list)) ≤ LENGTH ([1;2]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 4 ([1;2]:num list))) = ([1;2],2,T,T,F)``;
val _ = emit "sl_less_Nat_3_4" ``(LASTN (4+1) ([1;2]:num list),TL(LASTN (4+1) ([1;2]:num list)),LASTN 4 ([1;2]:num list),(4:num)+1 ≤ LENGTH ([1;2]:num list)) = ([1;2],[2],[1;2],F)``;
val _ = emit "sl_suffix_Nat_3_99" ``(LASTN 99 ([1;2]:num list),LENGTH(LASTN 99 ([1;2]:num list)),LENGTH(LASTN 99 ([1;2]:num list)) ≤ (99:num),LENGTH(LASTN 99 ([1;2]:num list)) ≤ LENGTH ([1;2]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 99 ([1;2]:num list))) = ([1;2],2,T,T,F)``;
val _ = emit "sl_less_Nat_3_99" ``(LASTN (99+1) ([1;2]:num list),TL(LASTN (99+1) ([1;2]:num list)),LASTN 99 ([1;2]:num list),(99:num)+1 ≤ LENGTH ([1;2]:num list)) = ([1;2],[2],[1;2],F)``;
val _ = emit "sl_suffix_Nat_3_900" ``(LASTN 900 ([1;2]:num list),LENGTH(LASTN 900 ([1;2]:num list)),LENGTH(LASTN 900 ([1;2]:num list)) ≤ (900:num),LENGTH(LASTN 900 ([1;2]:num list)) ≤ LENGTH ([1;2]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 900 ([1;2]:num list))) = ([1;2],2,T,T,F)``;
val _ = emit "sl_less_Nat_3_900" ``(LASTN (900+1) ([1;2]:num list),TL(LASTN (900+1) ([1;2]:num list)),LASTN 900 ([1;2]:num list),(900:num)+1 ≤ LENGTH ([1;2]:num list)) = ([1;2],[2],[1;2],F)``;
val _ = emit "sl_head_Nat_3" ``(LASTN (LENGTH ([1;2]:num list)) ([1;2]:num list), HD ([1;2]:num list)::LASTN (1) ([1;2]:num list)) = ([1;2],[1;2])``;
val _ = emit "sl_cons_Nat_3_0" ``LASTN (LENGTH ([1;2]:num list)+1) (0::([1;2]:num list)) = [0;1;2]``;
val _ = emit "sl_cons_Nat_3_99" ``LASTN (LENGTH ([1;2]:num list)+1) (99::([1;2]:num list)) = [99;1;2]``;
val _ = emit "sl_suffix_Nat_4_0" ``(LASTN 0 ([9;9]:num list),LENGTH(LASTN 0 ([9;9]:num list)),LENGTH(LASTN 0 ([9;9]:num list)) ≤ (0:num),LENGTH(LASTN 0 ([9;9]:num list)) ≤ LENGTH ([9;9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 0 ([9;9]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_4_0" ``(LASTN (0+1) ([9;9]:num list),TL(LASTN (0+1) ([9;9]:num list)),LASTN 0 ([9;9]:num list),(0:num)+1 ≤ LENGTH ([9;9]:num list)) = ([9],[],[],T)``;
val _ = emit "sl_suffix_Nat_4_1" ``(LASTN 1 ([9;9]:num list),LENGTH(LASTN 1 ([9;9]:num list)),LENGTH(LASTN 1 ([9;9]:num list)) ≤ (1:num),LENGTH(LASTN 1 ([9;9]:num list)) ≤ LENGTH ([9;9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 1 ([9;9]:num list))) = ([9],1,T,T,F)``;
val _ = emit "sl_less_Nat_4_1" ``(LASTN (1+1) ([9;9]:num list),TL(LASTN (1+1) ([9;9]:num list)),LASTN 1 ([9;9]:num list),(1:num)+1 ≤ LENGTH ([9;9]:num list)) = ([9;9],[9],[9],T)``;
val _ = emit "sl_suffix_Nat_4_2" ``(LASTN 2 ([9;9]:num list),LENGTH(LASTN 2 ([9;9]:num list)),LENGTH(LASTN 2 ([9;9]:num list)) ≤ (2:num),LENGTH(LASTN 2 ([9;9]:num list)) ≤ LENGTH ([9;9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 2 ([9;9]:num list))) = ([9;9],2,T,T,F)``;
val _ = emit "sl_less_Nat_4_2" ``(LASTN (2+1) ([9;9]:num list),TL(LASTN (2+1) ([9;9]:num list)),LASTN 2 ([9;9]:num list),(2:num)+1 ≤ LENGTH ([9;9]:num list)) = ([9;9],[9],[9;9],F)``;
val _ = emit "sl_suffix_Nat_4_3" ``(LASTN 3 ([9;9]:num list),LENGTH(LASTN 3 ([9;9]:num list)),LENGTH(LASTN 3 ([9;9]:num list)) ≤ (3:num),LENGTH(LASTN 3 ([9;9]:num list)) ≤ LENGTH ([9;9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 3 ([9;9]:num list))) = ([9;9],2,T,T,F)``;
val _ = emit "sl_less_Nat_4_3" ``(LASTN (3+1) ([9;9]:num list),TL(LASTN (3+1) ([9;9]:num list)),LASTN 3 ([9;9]:num list),(3:num)+1 ≤ LENGTH ([9;9]:num list)) = ([9;9],[9],[9;9],F)``;
val _ = emit "sl_suffix_Nat_4_4" ``(LASTN 4 ([9;9]:num list),LENGTH(LASTN 4 ([9;9]:num list)),LENGTH(LASTN 4 ([9;9]:num list)) ≤ (4:num),LENGTH(LASTN 4 ([9;9]:num list)) ≤ LENGTH ([9;9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 4 ([9;9]:num list))) = ([9;9],2,T,T,F)``;
val _ = emit "sl_less_Nat_4_4" ``(LASTN (4+1) ([9;9]:num list),TL(LASTN (4+1) ([9;9]:num list)),LASTN 4 ([9;9]:num list),(4:num)+1 ≤ LENGTH ([9;9]:num list)) = ([9;9],[9],[9;9],F)``;
val _ = emit "sl_suffix_Nat_4_99" ``(LASTN 99 ([9;9]:num list),LENGTH(LASTN 99 ([9;9]:num list)),LENGTH(LASTN 99 ([9;9]:num list)) ≤ (99:num),LENGTH(LASTN 99 ([9;9]:num list)) ≤ LENGTH ([9;9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 99 ([9;9]:num list))) = ([9;9],2,T,T,F)``;
val _ = emit "sl_less_Nat_4_99" ``(LASTN (99+1) ([9;9]:num list),TL(LASTN (99+1) ([9;9]:num list)),LASTN 99 ([9;9]:num list),(99:num)+1 ≤ LENGTH ([9;9]:num list)) = ([9;9],[9],[9;9],F)``;
val _ = emit "sl_suffix_Nat_4_900" ``(LASTN 900 ([9;9]:num list),LENGTH(LASTN 900 ([9;9]:num list)),LENGTH(LASTN 900 ([9;9]:num list)) ≤ (900:num),LENGTH(LASTN 900 ([9;9]:num list)) ≤ LENGTH ([9;9]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 900 ([9;9]:num list))) = ([9;9],2,T,T,F)``;
val _ = emit "sl_less_Nat_4_900" ``(LASTN (900+1) ([9;9]:num list),TL(LASTN (900+1) ([9;9]:num list)),LASTN 900 ([9;9]:num list),(900:num)+1 ≤ LENGTH ([9;9]:num list)) = ([9;9],[9],[9;9],F)``;
val _ = emit "sl_head_Nat_4" ``(LASTN (LENGTH ([9;9]:num list)) ([9;9]:num list), HD ([9;9]:num list)::LASTN (1) ([9;9]:num list)) = ([9;9],[9;9])``;
val _ = emit "sl_cons_Nat_4_0" ``LASTN (LENGTH ([9;9]:num list)+1) (0::([9;9]:num list)) = [0;9;9]``;
val _ = emit "sl_cons_Nat_4_99" ``LASTN (LENGTH ([9;9]:num list)+1) (99::([9;9]:num list)) = [99;9;9]``;
val _ = emit "sl_suffix_Nat_5_0" ``(LASTN 0 ([30;20;10]:num list),LENGTH(LASTN 0 ([30;20;10]:num list)),LENGTH(LASTN 0 ([30;20;10]:num list)) ≤ (0:num),LENGTH(LASTN 0 ([30;20;10]:num list)) ≤ LENGTH ([30;20;10]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 0 ([30;20;10]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_5_0" ``(LASTN (0+1) ([30;20;10]:num list),TL(LASTN (0+1) ([30;20;10]:num list)),LASTN 0 ([30;20;10]:num list),(0:num)+1 ≤ LENGTH ([30;20;10]:num list)) = ([10],[],[],T)``;
val _ = emit "sl_suffix_Nat_5_1" ``(LASTN 1 ([30;20;10]:num list),LENGTH(LASTN 1 ([30;20;10]:num list)),LENGTH(LASTN 1 ([30;20;10]:num list)) ≤ (1:num),LENGTH(LASTN 1 ([30;20;10]:num list)) ≤ LENGTH ([30;20;10]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 1 ([30;20;10]:num list))) = ([10],1,T,T,T)``;
val _ = emit "sl_less_Nat_5_1" ``(LASTN (1+1) ([30;20;10]:num list),TL(LASTN (1+1) ([30;20;10]:num list)),LASTN 1 ([30;20;10]:num list),(1:num)+1 ≤ LENGTH ([30;20;10]:num list)) = ([20;10],[10],[10],T)``;
val _ = emit "sl_suffix_Nat_5_2" ``(LASTN 2 ([30;20;10]:num list),LENGTH(LASTN 2 ([30;20;10]:num list)),LENGTH(LASTN 2 ([30;20;10]:num list)) ≤ (2:num),LENGTH(LASTN 2 ([30;20;10]:num list)) ≤ LENGTH ([30;20;10]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 2 ([30;20;10]:num list))) = ([20;10],2,T,T,T)``;
val _ = emit "sl_less_Nat_5_2" ``(LASTN (2+1) ([30;20;10]:num list),TL(LASTN (2+1) ([30;20;10]:num list)),LASTN 2 ([30;20;10]:num list),(2:num)+1 ≤ LENGTH ([30;20;10]:num list)) = ([30;20;10],[20;10],[20;10],T)``;
val _ = emit "sl_suffix_Nat_5_3" ``(LASTN 3 ([30;20;10]:num list),LENGTH(LASTN 3 ([30;20;10]:num list)),LENGTH(LASTN 3 ([30;20;10]:num list)) ≤ (3:num),LENGTH(LASTN 3 ([30;20;10]:num list)) ≤ LENGTH ([30;20;10]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 3 ([30;20;10]:num list))) = ([30;20;10],3,T,T,T)``;
val _ = emit "sl_less_Nat_5_3" ``(LASTN (3+1) ([30;20;10]:num list),TL(LASTN (3+1) ([30;20;10]:num list)),LASTN 3 ([30;20;10]:num list),(3:num)+1 ≤ LENGTH ([30;20;10]:num list)) = ([30;20;10],[20;10],[30;20;10],F)``;
val _ = emit "sl_suffix_Nat_5_4" ``(LASTN 4 ([30;20;10]:num list),LENGTH(LASTN 4 ([30;20;10]:num list)),LENGTH(LASTN 4 ([30;20;10]:num list)) ≤ (4:num),LENGTH(LASTN 4 ([30;20;10]:num list)) ≤ LENGTH ([30;20;10]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 4 ([30;20;10]:num list))) = ([30;20;10],3,T,T,T)``;
val _ = emit "sl_less_Nat_5_4" ``(LASTN (4+1) ([30;20;10]:num list),TL(LASTN (4+1) ([30;20;10]:num list)),LASTN 4 ([30;20;10]:num list),(4:num)+1 ≤ LENGTH ([30;20;10]:num list)) = ([30;20;10],[20;10],[30;20;10],F)``;
val _ = emit "sl_suffix_Nat_5_5" ``(LASTN 5 ([30;20;10]:num list),LENGTH(LASTN 5 ([30;20;10]:num list)),LENGTH(LASTN 5 ([30;20;10]:num list)) ≤ (5:num),LENGTH(LASTN 5 ([30;20;10]:num list)) ≤ LENGTH ([30;20;10]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 5 ([30;20;10]:num list))) = ([30;20;10],3,T,T,T)``;
val _ = emit "sl_less_Nat_5_5" ``(LASTN (5+1) ([30;20;10]:num list),TL(LASTN (5+1) ([30;20;10]:num list)),LASTN 5 ([30;20;10]:num list),(5:num)+1 ≤ LENGTH ([30;20;10]:num list)) = ([30;20;10],[20;10],[30;20;10],F)``;
val _ = emit "sl_suffix_Nat_5_99" ``(LASTN 99 ([30;20;10]:num list),LENGTH(LASTN 99 ([30;20;10]:num list)),LENGTH(LASTN 99 ([30;20;10]:num list)) ≤ (99:num),LENGTH(LASTN 99 ([30;20;10]:num list)) ≤ LENGTH ([30;20;10]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 99 ([30;20;10]:num list))) = ([30;20;10],3,T,T,T)``;
val _ = emit "sl_less_Nat_5_99" ``(LASTN (99+1) ([30;20;10]:num list),TL(LASTN (99+1) ([30;20;10]:num list)),LASTN 99 ([30;20;10]:num list),(99:num)+1 ≤ LENGTH ([30;20;10]:num list)) = ([30;20;10],[20;10],[30;20;10],F)``;
val _ = emit "sl_suffix_Nat_5_900" ``(LASTN 900 ([30;20;10]:num list),LENGTH(LASTN 900 ([30;20;10]:num list)),LENGTH(LASTN 900 ([30;20;10]:num list)) ≤ (900:num),LENGTH(LASTN 900 ([30;20;10]:num list)) ≤ LENGTH ([30;20;10]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 900 ([30;20;10]:num list))) = ([30;20;10],3,T,T,T)``;
val _ = emit "sl_less_Nat_5_900" ``(LASTN (900+1) ([30;20;10]:num list),TL(LASTN (900+1) ([30;20;10]:num list)),LASTN 900 ([30;20;10]:num list),(900:num)+1 ≤ LENGTH ([30;20;10]:num list)) = ([30;20;10],[20;10],[30;20;10],F)``;
val _ = emit "sl_head_Nat_5" ``(LASTN (LENGTH ([30;20;10]:num list)) ([30;20;10]:num list), HD ([30;20;10]:num list)::LASTN (2) ([30;20;10]:num list)) = ([30;20;10],[30;20;10])``;
val _ = emit "sl_cons_Nat_5_0" ``LASTN (LENGTH ([30;20;10]:num list)+1) (0::([30;20;10]:num list)) = [0;30;20;10]``;
val _ = emit "sl_cons_Nat_5_99" ``LASTN (LENGTH ([30;20;10]:num list)+1) (99::([30;20;10]:num list)) = [99;30;20;10]``;
val _ = emit "sl_suffix_Nat_6_0" ``(LASTN 0 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),LENGTH(LASTN 0 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LENGTH(LASTN 0 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ (0:num),LENGTH(LASTN 0 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 0 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Nat_6_0" ``(LASTN (0+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),TL(LASTN (0+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LASTN 0 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),(0:num)+1 ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([11],[],[],T)``;
val _ = emit "sl_suffix_Nat_6_1" ``(LASTN 1 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),LENGTH(LASTN 1 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LENGTH(LASTN 1 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ (1:num),LENGTH(LASTN 1 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 1 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list))) = ([11],1,T,T,F)``;
val _ = emit "sl_less_Nat_6_1" ``(LASTN (1+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),TL(LASTN (1+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LASTN 1 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),(1:num)+1 ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([10;11],[11],[11],T)``;
val _ = emit "sl_suffix_Nat_6_2" ``(LASTN 2 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),LENGTH(LASTN 2 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LENGTH(LASTN 2 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ (2:num),LENGTH(LASTN 2 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 2 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list))) = ([10;11],2,T,T,F)``;
val _ = emit "sl_less_Nat_6_2" ``(LASTN (2+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),TL(LASTN (2+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LASTN 2 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),(2:num)+1 ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([9;10;11],[10;11],[10;11],T)``;
val _ = emit "sl_suffix_Nat_6_11" ``(LASTN 11 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),LENGTH(LASTN 11 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LENGTH(LASTN 11 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ (11:num),LENGTH(LASTN 11 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 11 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list))) = ([1;2;3;4;5;6;7;8;9;10;11],11,T,T,F)``;
val _ = emit "sl_less_Nat_6_11" ``(LASTN (11+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),TL(LASTN (11+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LASTN 11 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),(11:num)+1 ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([0;1;2;3;4;5;6;7;8;9;10;11],[1;2;3;4;5;6;7;8;9;10;11],[1;2;3;4;5;6;7;8;9;10;11],T)``;
val _ = emit "sl_suffix_Nat_6_12" ``(LASTN 12 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),LENGTH(LASTN 12 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LENGTH(LASTN 12 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ (12:num),LENGTH(LASTN 12 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 12 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list))) = ([0;1;2;3;4;5;6;7;8;9;10;11],12,T,T,F)``;
val _ = emit "sl_less_Nat_6_12" ``(LASTN (12+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),TL(LASTN (12+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LASTN 12 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),(12:num)+1 ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([0;1;2;3;4;5;6;7;8;9;10;11],[1;2;3;4;5;6;7;8;9;10;11],[0;1;2;3;4;5;6;7;8;9;10;11],F)``;
val _ = emit "sl_suffix_Nat_6_13" ``(LASTN 13 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),LENGTH(LASTN 13 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LENGTH(LASTN 13 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ (13:num),LENGTH(LASTN 13 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 13 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list))) = ([0;1;2;3;4;5;6;7;8;9;10;11],12,T,T,F)``;
val _ = emit "sl_less_Nat_6_13" ``(LASTN (13+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),TL(LASTN (13+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LASTN 13 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),(13:num)+1 ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([0;1;2;3;4;5;6;7;8;9;10;11],[1;2;3;4;5;6;7;8;9;10;11],[0;1;2;3;4;5;6;7;8;9;10;11],F)``;
val _ = emit "sl_suffix_Nat_6_14" ``(LASTN 14 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),LENGTH(LASTN 14 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LENGTH(LASTN 14 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ (14:num),LENGTH(LASTN 14 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 14 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list))) = ([0;1;2;3;4;5;6;7;8;9;10;11],12,T,T,F)``;
val _ = emit "sl_less_Nat_6_14" ``(LASTN (14+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),TL(LASTN (14+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LASTN 14 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),(14:num)+1 ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([0;1;2;3;4;5;6;7;8;9;10;11],[1;2;3;4;5;6;7;8;9;10;11],[0;1;2;3;4;5;6;7;8;9;10;11],F)``;
val _ = emit "sl_suffix_Nat_6_99" ``(LASTN 99 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),LENGTH(LASTN 99 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LENGTH(LASTN 99 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ (99:num),LENGTH(LASTN 99 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 99 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list))) = ([0;1;2;3;4;5;6;7;8;9;10;11],12,T,T,F)``;
val _ = emit "sl_less_Nat_6_99" ``(LASTN (99+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),TL(LASTN (99+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LASTN 99 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),(99:num)+1 ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([0;1;2;3;4;5;6;7;8;9;10;11],[1;2;3;4;5;6;7;8;9;10;11],[0;1;2;3;4;5;6;7;8;9;10;11],F)``;
val _ = emit "sl_suffix_Nat_6_900" ``(LASTN 900 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),LENGTH(LASTN 900 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LENGTH(LASTN 900 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ (900:num),LENGTH(LASTN 900 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),EVERY (\x. x MOD 2 = 0) (LASTN 900 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list))) = ([0;1;2;3;4;5;6;7;8;9;10;11],12,T,T,F)``;
val _ = emit "sl_less_Nat_6_900" ``(LASTN (900+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),TL(LASTN (900+1) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)),LASTN 900 ([0;1;2;3;4;5;6;7;8;9;10;11]:num list),(900:num)+1 ≤ LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([0;1;2;3;4;5;6;7;8;9;10;11],[1;2;3;4;5;6;7;8;9;10;11],[0;1;2;3;4;5;6;7;8;9;10;11],F)``;
val _ = emit "sl_head_Nat_6" ``(LASTN (LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list), HD ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)::LASTN (11) ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = ([0;1;2;3;4;5;6;7;8;9;10;11],[0;1;2;3;4;5;6;7;8;9;10;11])``;
val _ = emit "sl_cons_Nat_6_0" ``LASTN (LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)+1) (0::([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = [0;0;1;2;3;4;5;6;7;8;9;10;11]``;
val _ = emit "sl_cons_Nat_6_99" ``LASTN (LENGTH ([0;1;2;3;4;5;6;7;8;9;10;11]:num list)+1) (99::([0;1;2;3;4;5;6;7;8;9;10;11]:num list)) = [99;0;1;2;3;4;5;6;7;8;9;10;11]``;
val _ = emit "sl_suffix_Bool_0_0" ``(LASTN 0 ([]:bool list),LENGTH(LASTN 0 ([]:bool list)),LENGTH(LASTN 0 ([]:bool list)) ≤ (0:num),LENGTH(LASTN 0 ([]:bool list)) ≤ LENGTH ([]:bool list),EVERY I (LASTN 0 ([]:bool list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Bool_0_0" ``(LASTN (0+1) ([]:bool list),TL(LASTN (0+1) ([]:bool list)),LASTN 0 ([]:bool list),(0:num)+1 ≤ LENGTH ([]:bool list)) = ([],[],[],F)``;
val _ = emit "sl_suffix_Bool_0_1" ``(LASTN 1 ([]:bool list),LENGTH(LASTN 1 ([]:bool list)),LENGTH(LASTN 1 ([]:bool list)) ≤ (1:num),LENGTH(LASTN 1 ([]:bool list)) ≤ LENGTH ([]:bool list),EVERY I (LASTN 1 ([]:bool list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Bool_0_1" ``(LASTN (1+1) ([]:bool list),TL(LASTN (1+1) ([]:bool list)),LASTN 1 ([]:bool list),(1:num)+1 ≤ LENGTH ([]:bool list)) = ([],[],[],F)``;
val _ = emit "sl_suffix_Bool_0_2" ``(LASTN 2 ([]:bool list),LENGTH(LASTN 2 ([]:bool list)),LENGTH(LASTN 2 ([]:bool list)) ≤ (2:num),LENGTH(LASTN 2 ([]:bool list)) ≤ LENGTH ([]:bool list),EVERY I (LASTN 2 ([]:bool list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Bool_0_2" ``(LASTN (2+1) ([]:bool list),TL(LASTN (2+1) ([]:bool list)),LASTN 2 ([]:bool list),(2:num)+1 ≤ LENGTH ([]:bool list)) = ([],[],[],F)``;
val _ = emit "sl_suffix_Bool_0_99" ``(LASTN 99 ([]:bool list),LENGTH(LASTN 99 ([]:bool list)),LENGTH(LASTN 99 ([]:bool list)) ≤ (99:num),LENGTH(LASTN 99 ([]:bool list)) ≤ LENGTH ([]:bool list),EVERY I (LASTN 99 ([]:bool list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Bool_0_99" ``(LASTN (99+1) ([]:bool list),TL(LASTN (99+1) ([]:bool list)),LASTN 99 ([]:bool list),(99:num)+1 ≤ LENGTH ([]:bool list)) = ([],[],[],F)``;
val _ = emit "sl_suffix_Bool_0_900" ``(LASTN 900 ([]:bool list),LENGTH(LASTN 900 ([]:bool list)),LENGTH(LASTN 900 ([]:bool list)) ≤ (900:num),LENGTH(LASTN 900 ([]:bool list)) ≤ LENGTH ([]:bool list),EVERY I (LASTN 900 ([]:bool list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Bool_0_900" ``(LASTN (900+1) ([]:bool list),TL(LASTN (900+1) ([]:bool list)),LASTN 900 ([]:bool list),(900:num)+1 ≤ LENGTH ([]:bool list)) = ([],[],[],F)``;
val _ = emit "sl_cons_Bool_0_0" ``LASTN (LENGTH ([]:bool list)+1) (F::([]:bool list)) = [F]``;
val _ = emit "sl_cons_Bool_0_1" ``LASTN (LENGTH ([]:bool list)+1) (T::([]:bool list)) = [T]``;
val _ = emit "sl_suffix_Bool_1_0" ``(LASTN 0 ([T]:bool list),LENGTH(LASTN 0 ([T]:bool list)),LENGTH(LASTN 0 ([T]:bool list)) ≤ (0:num),LENGTH(LASTN 0 ([T]:bool list)) ≤ LENGTH ([T]:bool list),EVERY I (LASTN 0 ([T]:bool list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Bool_1_0" ``(LASTN (0+1) ([T]:bool list),TL(LASTN (0+1) ([T]:bool list)),LASTN 0 ([T]:bool list),(0:num)+1 ≤ LENGTH ([T]:bool list)) = ([T],[],[],T)``;
val _ = emit "sl_suffix_Bool_1_1" ``(LASTN 1 ([T]:bool list),LENGTH(LASTN 1 ([T]:bool list)),LENGTH(LASTN 1 ([T]:bool list)) ≤ (1:num),LENGTH(LASTN 1 ([T]:bool list)) ≤ LENGTH ([T]:bool list),EVERY I (LASTN 1 ([T]:bool list))) = ([T],1,T,T,T)``;
val _ = emit "sl_less_Bool_1_1" ``(LASTN (1+1) ([T]:bool list),TL(LASTN (1+1) ([T]:bool list)),LASTN 1 ([T]:bool list),(1:num)+1 ≤ LENGTH ([T]:bool list)) = ([T],[],[T],F)``;
val _ = emit "sl_suffix_Bool_1_2" ``(LASTN 2 ([T]:bool list),LENGTH(LASTN 2 ([T]:bool list)),LENGTH(LASTN 2 ([T]:bool list)) ≤ (2:num),LENGTH(LASTN 2 ([T]:bool list)) ≤ LENGTH ([T]:bool list),EVERY I (LASTN 2 ([T]:bool list))) = ([T],1,T,T,T)``;
val _ = emit "sl_less_Bool_1_2" ``(LASTN (2+1) ([T]:bool list),TL(LASTN (2+1) ([T]:bool list)),LASTN 2 ([T]:bool list),(2:num)+1 ≤ LENGTH ([T]:bool list)) = ([T],[],[T],F)``;
val _ = emit "sl_suffix_Bool_1_3" ``(LASTN 3 ([T]:bool list),LENGTH(LASTN 3 ([T]:bool list)),LENGTH(LASTN 3 ([T]:bool list)) ≤ (3:num),LENGTH(LASTN 3 ([T]:bool list)) ≤ LENGTH ([T]:bool list),EVERY I (LASTN 3 ([T]:bool list))) = ([T],1,T,T,T)``;
val _ = emit "sl_less_Bool_1_3" ``(LASTN (3+1) ([T]:bool list),TL(LASTN (3+1) ([T]:bool list)),LASTN 3 ([T]:bool list),(3:num)+1 ≤ LENGTH ([T]:bool list)) = ([T],[],[T],F)``;
val _ = emit "sl_suffix_Bool_1_99" ``(LASTN 99 ([T]:bool list),LENGTH(LASTN 99 ([T]:bool list)),LENGTH(LASTN 99 ([T]:bool list)) ≤ (99:num),LENGTH(LASTN 99 ([T]:bool list)) ≤ LENGTH ([T]:bool list),EVERY I (LASTN 99 ([T]:bool list))) = ([T],1,T,T,T)``;
val _ = emit "sl_less_Bool_1_99" ``(LASTN (99+1) ([T]:bool list),TL(LASTN (99+1) ([T]:bool list)),LASTN 99 ([T]:bool list),(99:num)+1 ≤ LENGTH ([T]:bool list)) = ([T],[],[T],F)``;
val _ = emit "sl_suffix_Bool_1_900" ``(LASTN 900 ([T]:bool list),LENGTH(LASTN 900 ([T]:bool list)),LENGTH(LASTN 900 ([T]:bool list)) ≤ (900:num),LENGTH(LASTN 900 ([T]:bool list)) ≤ LENGTH ([T]:bool list),EVERY I (LASTN 900 ([T]:bool list))) = ([T],1,T,T,T)``;
val _ = emit "sl_less_Bool_1_900" ``(LASTN (900+1) ([T]:bool list),TL(LASTN (900+1) ([T]:bool list)),LASTN 900 ([T]:bool list),(900:num)+1 ≤ LENGTH ([T]:bool list)) = ([T],[],[T],F)``;
val _ = emit "sl_head_Bool_1" ``(LASTN (LENGTH ([T]:bool list)) ([T]:bool list), HD ([T]:bool list)::LASTN (0) ([T]:bool list)) = ([T],[T])``;
val _ = emit "sl_cons_Bool_1_0" ``LASTN (LENGTH ([T]:bool list)+1) (F::([T]:bool list)) = [F;T]``;
val _ = emit "sl_cons_Bool_1_1" ``LASTN (LENGTH ([T]:bool list)+1) (T::([T]:bool list)) = [T;T]``;
val _ = emit "sl_suffix_Bool_2_0" ``(LASTN 0 ([F]:bool list),LENGTH(LASTN 0 ([F]:bool list)),LENGTH(LASTN 0 ([F]:bool list)) ≤ (0:num),LENGTH(LASTN 0 ([F]:bool list)) ≤ LENGTH ([F]:bool list),EVERY I (LASTN 0 ([F]:bool list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Bool_2_0" ``(LASTN (0+1) ([F]:bool list),TL(LASTN (0+1) ([F]:bool list)),LASTN 0 ([F]:bool list),(0:num)+1 ≤ LENGTH ([F]:bool list)) = ([F],[],[],T)``;
val _ = emit "sl_suffix_Bool_2_1" ``(LASTN 1 ([F]:bool list),LENGTH(LASTN 1 ([F]:bool list)),LENGTH(LASTN 1 ([F]:bool list)) ≤ (1:num),LENGTH(LASTN 1 ([F]:bool list)) ≤ LENGTH ([F]:bool list),EVERY I (LASTN 1 ([F]:bool list))) = ([F],1,T,T,F)``;
val _ = emit "sl_less_Bool_2_1" ``(LASTN (1+1) ([F]:bool list),TL(LASTN (1+1) ([F]:bool list)),LASTN 1 ([F]:bool list),(1:num)+1 ≤ LENGTH ([F]:bool list)) = ([F],[],[F],F)``;
val _ = emit "sl_suffix_Bool_2_2" ``(LASTN 2 ([F]:bool list),LENGTH(LASTN 2 ([F]:bool list)),LENGTH(LASTN 2 ([F]:bool list)) ≤ (2:num),LENGTH(LASTN 2 ([F]:bool list)) ≤ LENGTH ([F]:bool list),EVERY I (LASTN 2 ([F]:bool list))) = ([F],1,T,T,F)``;
val _ = emit "sl_less_Bool_2_2" ``(LASTN (2+1) ([F]:bool list),TL(LASTN (2+1) ([F]:bool list)),LASTN 2 ([F]:bool list),(2:num)+1 ≤ LENGTH ([F]:bool list)) = ([F],[],[F],F)``;
val _ = emit "sl_suffix_Bool_2_3" ``(LASTN 3 ([F]:bool list),LENGTH(LASTN 3 ([F]:bool list)),LENGTH(LASTN 3 ([F]:bool list)) ≤ (3:num),LENGTH(LASTN 3 ([F]:bool list)) ≤ LENGTH ([F]:bool list),EVERY I (LASTN 3 ([F]:bool list))) = ([F],1,T,T,F)``;
val _ = emit "sl_less_Bool_2_3" ``(LASTN (3+1) ([F]:bool list),TL(LASTN (3+1) ([F]:bool list)),LASTN 3 ([F]:bool list),(3:num)+1 ≤ LENGTH ([F]:bool list)) = ([F],[],[F],F)``;
val _ = emit "sl_suffix_Bool_2_99" ``(LASTN 99 ([F]:bool list),LENGTH(LASTN 99 ([F]:bool list)),LENGTH(LASTN 99 ([F]:bool list)) ≤ (99:num),LENGTH(LASTN 99 ([F]:bool list)) ≤ LENGTH ([F]:bool list),EVERY I (LASTN 99 ([F]:bool list))) = ([F],1,T,T,F)``;
val _ = emit "sl_less_Bool_2_99" ``(LASTN (99+1) ([F]:bool list),TL(LASTN (99+1) ([F]:bool list)),LASTN 99 ([F]:bool list),(99:num)+1 ≤ LENGTH ([F]:bool list)) = ([F],[],[F],F)``;
val _ = emit "sl_suffix_Bool_2_900" ``(LASTN 900 ([F]:bool list),LENGTH(LASTN 900 ([F]:bool list)),LENGTH(LASTN 900 ([F]:bool list)) ≤ (900:num),LENGTH(LASTN 900 ([F]:bool list)) ≤ LENGTH ([F]:bool list),EVERY I (LASTN 900 ([F]:bool list))) = ([F],1,T,T,F)``;
val _ = emit "sl_less_Bool_2_900" ``(LASTN (900+1) ([F]:bool list),TL(LASTN (900+1) ([F]:bool list)),LASTN 900 ([F]:bool list),(900:num)+1 ≤ LENGTH ([F]:bool list)) = ([F],[],[F],F)``;
val _ = emit "sl_head_Bool_2" ``(LASTN (LENGTH ([F]:bool list)) ([F]:bool list), HD ([F]:bool list)::LASTN (0) ([F]:bool list)) = ([F],[F])``;
val _ = emit "sl_cons_Bool_2_0" ``LASTN (LENGTH ([F]:bool list)+1) (F::([F]:bool list)) = [F;F]``;
val _ = emit "sl_cons_Bool_2_1" ``LASTN (LENGTH ([F]:bool list)+1) (T::([F]:bool list)) = [T;F]``;
val _ = emit "sl_suffix_Bool_3_0" ``(LASTN 0 ([T;F]:bool list),LENGTH(LASTN 0 ([T;F]:bool list)),LENGTH(LASTN 0 ([T;F]:bool list)) ≤ (0:num),LENGTH(LASTN 0 ([T;F]:bool list)) ≤ LENGTH ([T;F]:bool list),EVERY I (LASTN 0 ([T;F]:bool list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Bool_3_0" ``(LASTN (0+1) ([T;F]:bool list),TL(LASTN (0+1) ([T;F]:bool list)),LASTN 0 ([T;F]:bool list),(0:num)+1 ≤ LENGTH ([T;F]:bool list)) = ([F],[],[],T)``;
val _ = emit "sl_suffix_Bool_3_1" ``(LASTN 1 ([T;F]:bool list),LENGTH(LASTN 1 ([T;F]:bool list)),LENGTH(LASTN 1 ([T;F]:bool list)) ≤ (1:num),LENGTH(LASTN 1 ([T;F]:bool list)) ≤ LENGTH ([T;F]:bool list),EVERY I (LASTN 1 ([T;F]:bool list))) = ([F],1,T,T,F)``;
val _ = emit "sl_less_Bool_3_1" ``(LASTN (1+1) ([T;F]:bool list),TL(LASTN (1+1) ([T;F]:bool list)),LASTN 1 ([T;F]:bool list),(1:num)+1 ≤ LENGTH ([T;F]:bool list)) = ([T;F],[F],[F],T)``;
val _ = emit "sl_suffix_Bool_3_2" ``(LASTN 2 ([T;F]:bool list),LENGTH(LASTN 2 ([T;F]:bool list)),LENGTH(LASTN 2 ([T;F]:bool list)) ≤ (2:num),LENGTH(LASTN 2 ([T;F]:bool list)) ≤ LENGTH ([T;F]:bool list),EVERY I (LASTN 2 ([T;F]:bool list))) = ([T;F],2,T,T,F)``;
val _ = emit "sl_less_Bool_3_2" ``(LASTN (2+1) ([T;F]:bool list),TL(LASTN (2+1) ([T;F]:bool list)),LASTN 2 ([T;F]:bool list),(2:num)+1 ≤ LENGTH ([T;F]:bool list)) = ([T;F],[F],[T;F],F)``;
val _ = emit "sl_suffix_Bool_3_3" ``(LASTN 3 ([T;F]:bool list),LENGTH(LASTN 3 ([T;F]:bool list)),LENGTH(LASTN 3 ([T;F]:bool list)) ≤ (3:num),LENGTH(LASTN 3 ([T;F]:bool list)) ≤ LENGTH ([T;F]:bool list),EVERY I (LASTN 3 ([T;F]:bool list))) = ([T;F],2,T,T,F)``;
val _ = emit "sl_less_Bool_3_3" ``(LASTN (3+1) ([T;F]:bool list),TL(LASTN (3+1) ([T;F]:bool list)),LASTN 3 ([T;F]:bool list),(3:num)+1 ≤ LENGTH ([T;F]:bool list)) = ([T;F],[F],[T;F],F)``;
val _ = emit "sl_suffix_Bool_3_4" ``(LASTN 4 ([T;F]:bool list),LENGTH(LASTN 4 ([T;F]:bool list)),LENGTH(LASTN 4 ([T;F]:bool list)) ≤ (4:num),LENGTH(LASTN 4 ([T;F]:bool list)) ≤ LENGTH ([T;F]:bool list),EVERY I (LASTN 4 ([T;F]:bool list))) = ([T;F],2,T,T,F)``;
val _ = emit "sl_less_Bool_3_4" ``(LASTN (4+1) ([T;F]:bool list),TL(LASTN (4+1) ([T;F]:bool list)),LASTN 4 ([T;F]:bool list),(4:num)+1 ≤ LENGTH ([T;F]:bool list)) = ([T;F],[F],[T;F],F)``;
val _ = emit "sl_suffix_Bool_3_99" ``(LASTN 99 ([T;F]:bool list),LENGTH(LASTN 99 ([T;F]:bool list)),LENGTH(LASTN 99 ([T;F]:bool list)) ≤ (99:num),LENGTH(LASTN 99 ([T;F]:bool list)) ≤ LENGTH ([T;F]:bool list),EVERY I (LASTN 99 ([T;F]:bool list))) = ([T;F],2,T,T,F)``;
val _ = emit "sl_less_Bool_3_99" ``(LASTN (99+1) ([T;F]:bool list),TL(LASTN (99+1) ([T;F]:bool list)),LASTN 99 ([T;F]:bool list),(99:num)+1 ≤ LENGTH ([T;F]:bool list)) = ([T;F],[F],[T;F],F)``;
val _ = emit "sl_suffix_Bool_3_900" ``(LASTN 900 ([T;F]:bool list),LENGTH(LASTN 900 ([T;F]:bool list)),LENGTH(LASTN 900 ([T;F]:bool list)) ≤ (900:num),LENGTH(LASTN 900 ([T;F]:bool list)) ≤ LENGTH ([T;F]:bool list),EVERY I (LASTN 900 ([T;F]:bool list))) = ([T;F],2,T,T,F)``;
val _ = emit "sl_less_Bool_3_900" ``(LASTN (900+1) ([T;F]:bool list),TL(LASTN (900+1) ([T;F]:bool list)),LASTN 900 ([T;F]:bool list),(900:num)+1 ≤ LENGTH ([T;F]:bool list)) = ([T;F],[F],[T;F],F)``;
val _ = emit "sl_head_Bool_3" ``(LASTN (LENGTH ([T;F]:bool list)) ([T;F]:bool list), HD ([T;F]:bool list)::LASTN (1) ([T;F]:bool list)) = ([T;F],[T;F])``;
val _ = emit "sl_cons_Bool_3_0" ``LASTN (LENGTH ([T;F]:bool list)+1) (F::([T;F]:bool list)) = [F;T;F]``;
val _ = emit "sl_cons_Bool_3_1" ``LASTN (LENGTH ([T;F]:bool list)+1) (T::([T;F]:bool list)) = [T;T;F]``;
val _ = emit "sl_suffix_Bool_4_0" ``(LASTN 0 ([F;T;F]:bool list),LENGTH(LASTN 0 ([F;T;F]:bool list)),LENGTH(LASTN 0 ([F;T;F]:bool list)) ≤ (0:num),LENGTH(LASTN 0 ([F;T;F]:bool list)) ≤ LENGTH ([F;T;F]:bool list),EVERY I (LASTN 0 ([F;T;F]:bool list))) = ([],0,T,T,T)``;
val _ = emit "sl_less_Bool_4_0" ``(LASTN (0+1) ([F;T;F]:bool list),TL(LASTN (0+1) ([F;T;F]:bool list)),LASTN 0 ([F;T;F]:bool list),(0:num)+1 ≤ LENGTH ([F;T;F]:bool list)) = ([F],[],[],T)``;
val _ = emit "sl_suffix_Bool_4_1" ``(LASTN 1 ([F;T;F]:bool list),LENGTH(LASTN 1 ([F;T;F]:bool list)),LENGTH(LASTN 1 ([F;T;F]:bool list)) ≤ (1:num),LENGTH(LASTN 1 ([F;T;F]:bool list)) ≤ LENGTH ([F;T;F]:bool list),EVERY I (LASTN 1 ([F;T;F]:bool list))) = ([F],1,T,T,F)``;
val _ = emit "sl_less_Bool_4_1" ``(LASTN (1+1) ([F;T;F]:bool list),TL(LASTN (1+1) ([F;T;F]:bool list)),LASTN 1 ([F;T;F]:bool list),(1:num)+1 ≤ LENGTH ([F;T;F]:bool list)) = ([T;F],[F],[F],T)``;
val _ = emit "sl_suffix_Bool_4_2" ``(LASTN 2 ([F;T;F]:bool list),LENGTH(LASTN 2 ([F;T;F]:bool list)),LENGTH(LASTN 2 ([F;T;F]:bool list)) ≤ (2:num),LENGTH(LASTN 2 ([F;T;F]:bool list)) ≤ LENGTH ([F;T;F]:bool list),EVERY I (LASTN 2 ([F;T;F]:bool list))) = ([T;F],2,T,T,F)``;
val _ = emit "sl_less_Bool_4_2" ``(LASTN (2+1) ([F;T;F]:bool list),TL(LASTN (2+1) ([F;T;F]:bool list)),LASTN 2 ([F;T;F]:bool list),(2:num)+1 ≤ LENGTH ([F;T;F]:bool list)) = ([F;T;F],[T;F],[T;F],T)``;
val _ = emit "sl_suffix_Bool_4_3" ``(LASTN 3 ([F;T;F]:bool list),LENGTH(LASTN 3 ([F;T;F]:bool list)),LENGTH(LASTN 3 ([F;T;F]:bool list)) ≤ (3:num),LENGTH(LASTN 3 ([F;T;F]:bool list)) ≤ LENGTH ([F;T;F]:bool list),EVERY I (LASTN 3 ([F;T;F]:bool list))) = ([F;T;F],3,T,T,F)``;
val _ = emit "sl_less_Bool_4_3" ``(LASTN (3+1) ([F;T;F]:bool list),TL(LASTN (3+1) ([F;T;F]:bool list)),LASTN 3 ([F;T;F]:bool list),(3:num)+1 ≤ LENGTH ([F;T;F]:bool list)) = ([F;T;F],[T;F],[F;T;F],F)``;
val _ = emit "sl_suffix_Bool_4_4" ``(LASTN 4 ([F;T;F]:bool list),LENGTH(LASTN 4 ([F;T;F]:bool list)),LENGTH(LASTN 4 ([F;T;F]:bool list)) ≤ (4:num),LENGTH(LASTN 4 ([F;T;F]:bool list)) ≤ LENGTH ([F;T;F]:bool list),EVERY I (LASTN 4 ([F;T;F]:bool list))) = ([F;T;F],3,T,T,F)``;
val _ = emit "sl_less_Bool_4_4" ``(LASTN (4+1) ([F;T;F]:bool list),TL(LASTN (4+1) ([F;T;F]:bool list)),LASTN 4 ([F;T;F]:bool list),(4:num)+1 ≤ LENGTH ([F;T;F]:bool list)) = ([F;T;F],[T;F],[F;T;F],F)``;
val _ = emit "sl_suffix_Bool_4_5" ``(LASTN 5 ([F;T;F]:bool list),LENGTH(LASTN 5 ([F;T;F]:bool list)),LENGTH(LASTN 5 ([F;T;F]:bool list)) ≤ (5:num),LENGTH(LASTN 5 ([F;T;F]:bool list)) ≤ LENGTH ([F;T;F]:bool list),EVERY I (LASTN 5 ([F;T;F]:bool list))) = ([F;T;F],3,T,T,F)``;
val _ = emit "sl_less_Bool_4_5" ``(LASTN (5+1) ([F;T;F]:bool list),TL(LASTN (5+1) ([F;T;F]:bool list)),LASTN 5 ([F;T;F]:bool list),(5:num)+1 ≤ LENGTH ([F;T;F]:bool list)) = ([F;T;F],[T;F],[F;T;F],F)``;
val _ = emit "sl_suffix_Bool_4_99" ``(LASTN 99 ([F;T;F]:bool list),LENGTH(LASTN 99 ([F;T;F]:bool list)),LENGTH(LASTN 99 ([F;T;F]:bool list)) ≤ (99:num),LENGTH(LASTN 99 ([F;T;F]:bool list)) ≤ LENGTH ([F;T;F]:bool list),EVERY I (LASTN 99 ([F;T;F]:bool list))) = ([F;T;F],3,T,T,F)``;
val _ = emit "sl_less_Bool_4_99" ``(LASTN (99+1) ([F;T;F]:bool list),TL(LASTN (99+1) ([F;T;F]:bool list)),LASTN 99 ([F;T;F]:bool list),(99:num)+1 ≤ LENGTH ([F;T;F]:bool list)) = ([F;T;F],[T;F],[F;T;F],F)``;
val _ = emit "sl_suffix_Bool_4_900" ``(LASTN 900 ([F;T;F]:bool list),LENGTH(LASTN 900 ([F;T;F]:bool list)),LENGTH(LASTN 900 ([F;T;F]:bool list)) ≤ (900:num),LENGTH(LASTN 900 ([F;T;F]:bool list)) ≤ LENGTH ([F;T;F]:bool list),EVERY I (LASTN 900 ([F;T;F]:bool list))) = ([F;T;F],3,T,T,F)``;
val _ = emit "sl_less_Bool_4_900" ``(LASTN (900+1) ([F;T;F]:bool list),TL(LASTN (900+1) ([F;T;F]:bool list)),LASTN 900 ([F;T;F]:bool list),(900:num)+1 ≤ LENGTH ([F;T;F]:bool list)) = ([F;T;F],[T;F],[F;T;F],F)``;
val _ = emit "sl_head_Bool_4" ``(LASTN (LENGTH ([F;T;F]:bool list)) ([F;T;F]:bool list), HD ([F;T;F]:bool list)::LASTN (2) ([F;T;F]:bool list)) = ([F;T;F],[F;T;F])``;
val _ = emit "sl_cons_Bool_4_0" ``LASTN (LENGTH ([F;T;F]:bool list)+1) (F::([F;T;F]:bool list)) = [F;F;T;F]``;
val _ = emit "sl_cons_Bool_4_1" ``LASTN (LENGTH ([F;T;F]:bool list)+1) (T::([F;T;F]:bool list)) = [T;F;T;F]``;
