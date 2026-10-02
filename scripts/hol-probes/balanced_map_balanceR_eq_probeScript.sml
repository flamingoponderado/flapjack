load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse Tactic Rewrite simpLib bossLib Tactical BasicProvers arithmeticTheory comparisonTheory pred_setTheory finite_mapTheory balanced_mapTheory;
val _ = Globals.linewidth := 10000;
val structure_size_thm = prove (``!cmp t. invariant cmp t ==> size t = structure_size t``, Cases_on `t` >> rw [size_def,invariant_def,structure_size_def]);
val balanceR_balR = prove (``!k v l r cmp.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  balanceR k v l r = balR k v l r``,
Tactic.HO_MATCH_MP_TAC balanceR_ind >>
 rw [] >>
 rw [balanceR_def, balR_def, rotateL_def, doubleL_def, bin_def, singleL_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 fs [size_def, invariant_def, structure_size_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 fs [balanced_def] >>
 TRY (Cases_on `l` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (Cases_on `r` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (Cases_on `v4` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (fs [ratio_def] >> NO_TAC) >>
 every_case_tac >>
 fs [size_def, structure_size_def, ratio_def, delta_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 fs [invariant_def, doubleL_def, bin_def, size_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 rw []);
val _ = if null(hyp balanceR_balR) then () else raise Fail "open balanceR equality hypotheses";
val _ = (print "bmbr_full="; Globals.show_types := true; print_thm balanceR_balR; print "\n");
val _ = (print "bmbr_empty="; print_term(rand(concl(EVAL ``balanceR 1 50 Tip Tip = balR 1 50 Tip Tip``))); print "\n");
val _ = (print "bmbr_singleton="; print_term(rand(concl(EVAL ``balanceR 1 50 Tip (Bin 1 6 6 Tip Tip) = balR 1 50 Tip (Bin 1 6 6 Tip Tip)``))); print "\n");
val _ = (print "bmbr_lr_only="; print_term(rand(concl(EVAL ``balanceR 1 50 Tip (Bin 2 6 6 (Bin 1 5 5 Tip Tip) Tip) = balR 1 50 Tip (Bin 2 6 6 (Bin 1 5 5 Tip Tip) Tip)``))); print "\n");
val _ = (print "bmbr_ll_only="; print_term(rand(concl(EVAL ``balanceR 1 50 Tip (Bin 2 5 5 Tip (Bin 1 6 6 Tip Tip)) = balR 1 50 Tip (Bin 2 5 5 Tip (Bin 1 6 6 Tip Tip))``))); print "\n");
val _ = (print "bmbr_single_tip="; print_term(rand(concl(EVAL ``balanceR 1 50 Tip (Bin 3 5 5 (Bin 1 4 4 Tip Tip) (Bin 1 6 6 Tip Tip)) = balR 1 50 Tip (Bin 3 5 5 (Bin 1 4 4 Tip Tip) (Bin 1 6 6 Tip Tip))``))); print "\n");
val _ = (print "bmbr_double_tip="; print_term(rand(concl(EVAL ``balanceR 1 50 Tip (Bin 4 5 5 (Bin 2 4 4 (Bin 1 3 3 Tip Tip) Tip) (Bin 1 6 6 Tip Tip)) = balR 1 50 Tip (Bin 4 5 5 (Bin 2 4 4 (Bin 1 3 3 Tip Tip) Tip) (Bin 1 6 6 Tip Tip))``))); print "\n");
val _ = (print "bmbr_left_tip="; print_term(rand(concl(EVAL ``balanceR 1 50 (Bin 1 0 0 Tip Tip) Tip = balR 1 50 (Bin 1 0 0 Tip Tip) Tip``))); print "\n");
val _ = (print "bmbr_fallback="; print_term(rand(concl(EVAL ``balanceR 1 50 (Bin 1 0 0 Tip Tip) (Bin 2 5 5 Tip (Bin 1 6 6 Tip Tip)) = balR 1 50 (Bin 1 0 0 Tip Tip) (Bin 2 5 5 Tip (Bin 1 6 6 Tip Tip))``))); print "\n");
val _ = (print "bmbr_heavy_single="; print_term(rand(concl(EVAL ``balanceR 1 50 (Bin 1 0 0 Tip Tip) (Bin 4 4 4 (Bin 1 3 3 Tip Tip) (Bin 2 5 5 Tip (Bin 1 6 6 Tip Tip))) = balR 1 50 (Bin 1 0 0 Tip Tip) (Bin 4 4 4 (Bin 1 3 3 Tip Tip) (Bin 2 5 5 Tip (Bin 1 6 6 Tip Tip)))``))); print "\n");
val _ = (print "bmbr_heavy_double="; print_term(rand(concl(EVAL ``balanceR 1 50 (Bin 1 0 0 Tip Tip) (Bin 4 5 5 (Bin 2 4 4 (Bin 1 3 3 Tip Tip) Tip) (Bin 1 6 6 Tip Tip)) = balR 1 50 (Bin 1 0 0 Tip Tip) (Bin 4 5 5 (Bin 2 4 4 (Bin 1 3 3 Tip Tip) Tip) (Bin 1 6 6 Tip Tip))``))); print "\n");
