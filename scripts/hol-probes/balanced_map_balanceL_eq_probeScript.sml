load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse Tactic Rewrite simpLib bossLib Tactical BasicProvers arithmeticTheory comparisonTheory pred_setTheory finite_mapTheory balanced_mapTheory;
val _ = Globals.linewidth := 10000;
val key_ordered_to_fmap = Tactical.prove (``!cmp k t res. good_cmp cmp ==> (key_ordered cmp k t res <=> !ks. ks IN FDOM (to_fmap cmp t) ==> key_set_cmp cmp k ks res)``, Tactical.THEN (Induct_on `t`, Tactical.THEN (rw [key_ordered_def,to_fmap_def], Tactical.THEN (Tactic.EQ_TAC, Tactical.THEN (rw [], metis_tac [key_set_cmp_thm])))));
val replay = prove(concl invariant_eq,
  rw [invariant_def] >> Tactic.EQ_TAC >> rw [DISJOINT_DEF, EXTENSION] >>
  Tactic.CCONTR_TAC >> fs [] >> Tactic.IMP_RES_TAC key_ordered_to_fmap >>
  Tactic.IMP_RES_TAC to_fmap_key_set >> gvs [key_set_cmp_thm] >>
  metis_tac [comparisonTheory.cmp_thms]);
val _ = if null(hyp replay) then () else raise Fail "open replay hypotheses";
val inv_props = prove(``!cmp s k v l r. good_cmp cmp /\ invariant cmp (Bin s k v l r) ==> DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r)) /\ (!x. key_set cmp x IN FDOM (to_fmap cmp l) ==> cmp k x = Greater) /\ (!x. key_set cmp x IN FDOM (to_fmap cmp r) ==> cmp k x = Less)``,
  rw [invariant_eq] >> Tactic.IMP_RES_TAC key_ordered_to_fmap >> rfs [key_set_cmp_thm]);
val _ = if null(hyp inv_props) then () else raise Fail "open inv_props hypotheses";
val TIMES_MIN = prove (``!x y z. x * MIN y z = MIN (x * y) (x * z)``, rw [MIN_DEF] >> fs []);
val balanced_lem3 = prove (``!b b0 r.
     almost_balancedL (b + b0 + 1) r ∧
     b + b0 + 1 > delta * r ∧
     b0 < ratio * b ∧
     balanced b b0
   ⇒
     balanced b (b0 + r + 1) ∧
     balanced b0 r``, rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def, ratio_def]);

val structure_size_thm = prove (``!cmp t. invariant cmp t ==> size t = structure_size t``, Cases_on `t` >> rw [size_def,invariant_def,structure_size_def]);
val balanced_lem4 = prove (``!b b' b0' r.
  almost_balancedL (b + b' + b0' + 2) r ∧
  b + b' + b0' + 2 > delta * r ∧
  ¬(b' + b0' + 1 < ratio * b) ∧
  balanced b (b' + b0' + 1) ∧
  balanced b' b0'
  ⇒
  balanced (b + b' + 1) (b0' + r + 1) ∧
  balanced b b' ∧
  balanced b0' r``, rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def, ratio_def]);

val good_cmp_greater_antisym = prove (``  good_cmp cmp ∧
  cmp x y = Greater ∧
  cmp y x = Greater ⇒
  F``,
  rewrite_tac [cmp_thms |> Drule.CONJUNCTS |> last]
  \\ strip_tac
  \\ last_x_assum kall_tac
  \\ last_x_assum kall_tac
  \\ pop_assum mp_tac
  \\ last_x_assum $ simp_tac (srw_ss()) o single
  \\ asm_rewrite_tac []
  \\ simp_tac (srw_ss()) []);

val balanceL_balL = prove (``!k v l r cmp.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  balanceL k v l r = balL k v l r``,
 Tactic.HO_MATCH_MP_TAC balanceL_ind >>
 rw [] >>
 rw [balanceL_def, balL_def, rotateR_def, doubleR_def, bin_def, singleR_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 fs [size_def, invariant_def, structure_size_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 fs [balanced_def] >>
 TRY (Cases_on `l` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (Cases_on `r` >> fs [structure_size_def, size_def] >> NO_TAC) >>
 TRY (fs [ratio_def] >> NO_TAC) >>
 gvs [size_def, structure_size_def, ratio_def, delta_def,
     invariant_def, doubleR_def, bin_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 gvs [size_def, structure_size_def, ratio_def, delta_def,
     invariant_def, doubleR_def, bin_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 rw [] >>
 every_case_tac >>
 gvs [invariant_def, doubleR_def, bin_def,
      size_def, structure_size_def, ratio_def, delta_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 gvs []);
val _ = if null(hyp balanceL_balL) then () else raise Fail "open balanceL equality hypotheses";
val _ = (print "bmbl_full="; Globals.show_types := true; print_thm balanceL_balL; print "\n");
val _ = (print "bmbl_empty="; print_term(rand(concl(EVAL ``balanceL 5 50 Tip Tip = balL 5 50 Tip Tip``))); print "\n");
val _ = (print "bmbl_singleton="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 1 0 0 Tip Tip) Tip = balL 5 50 (Bin 1 0 0 Tip Tip) Tip``))); print "\n");
val _ = (print "bmbl_lr_only="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 2 0 0 Tip (Bin 1 1 1 Tip Tip)) Tip = balL 5 50 (Bin 2 0 0 Tip (Bin 1 1 1 Tip Tip)) Tip``))); print "\n");
val _ = (print "bmbl_ll_only="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 2 1 1 (Bin 1 0 0 Tip Tip) Tip) Tip = balL 5 50 (Bin 2 1 1 (Bin 1 0 0 Tip Tip) Tip) Tip``))); print "\n");
val _ = (print "bmbl_single_tip="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 3 1 1 (Bin 1 0 0 Tip Tip) (Bin 1 2 2 Tip Tip)) Tip = balL 5 50 (Bin 3 1 1 (Bin 1 0 0 Tip Tip) (Bin 1 2 2 Tip Tip)) Tip``))); print "\n");
val _ = (print "bmbl_double_tip="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) Tip = balL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) Tip``))); print "\n");
val _ = (print "bmbl_left_tip="; print_term(rand(concl(EVAL ``balanceL 5 50 Tip (Bin 1 6 6 Tip Tip) = balL 5 50 Tip (Bin 1 6 6 Tip Tip)``))); print "\n");
val _ = (print "bmbl_fallback="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 2 1 1 (Bin 1 0 0 Tip Tip) Tip) (Bin 1 6 6 Tip Tip) = balL 5 50 (Bin 2 1 1 (Bin 1 0 0 Tip Tip) Tip) (Bin 1 6 6 Tip Tip)``))); print "\n");
val _ = (print "bmbl_heavy_single="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 4 2 2 (Bin 2 1 1 (Bin 1 0 0 Tip Tip) Tip) (Bin 1 3 3 Tip Tip)) (Bin 1 6 6 Tip Tip) = balL 5 50 (Bin 4 2 2 (Bin 2 1 1 (Bin 1 0 0 Tip Tip) Tip) (Bin 1 3 3 Tip Tip)) (Bin 1 6 6 Tip Tip)``))); print "\n");
val _ = (print "bmbl_heavy_double="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) (Bin 1 6 6 Tip Tip) = balL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) (Bin 1 6 6 Tip Tip)``))); print "\n");
