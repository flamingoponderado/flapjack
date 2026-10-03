load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib Tactical BasicProvers arithmeticTheory comparisonTheory pred_setTheory finite_mapTheory balanced_mapTheory;
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
val singleR_thm = prove (``!k v r cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL n (size r) ∧
  ¬(size r + n ≤ 1) ∧
  n > delta * size r ∧
  size b0 < ratio * size b ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp r
 ⇒
  invariant cmp (singleR k v (Bin n k' v' b b0) r) ∧
  to_fmap cmp (singleR k v (Bin n k' v' b b0) r) =
    (to_fmap cmp (Bin n k' v' b b0) ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``,
 rw [singleR_def] >>
 Tactic.IMP_RES_TAC inv_props
 >- (fs [invariant_def, bin_def, size_def, structure_size_def, bin_def,
         key_ordered_def] >>
     Tactic.IMP_RES_TAC structure_size_thm >>
     rw [size_def] >>
     rfs [size_def, key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, balanced_lem3,
                ADD_ASSOC])
 >- (rw [to_fmap_def, bin_def, FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [to_fmap_def, invariant_def, key_ordered_def] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, FUPDATE_COMMUTES,
                FUNION_ASSOC]));
val _ = if null(hyp singleR_thm) then () else raise Fail "open singleR theorem hypotheses";
val _ = (print "bmsr_full="; Globals.show_types := true; print_thm singleR_thm; print "\n");
val _ = (print "bmsr_tree="; print_term(rand(concl(EVAL ``singleR 2 20 (Bin 2 1 10 (Bin 1 0 0 Tip Tip) Tip) Tip``))); print "\n");
val _ = (print "bmsr_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (singleR 2 20 (Bin 2 1 10 (Bin 1 0 0 Tip Tip) Tip) Tip)``))); print "\n");
val _ = (print "bmsr_lookup0="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 0 (singleR 2 20 (Bin 2 1 10 (Bin 1 0 0 Tip Tip) Tip) Tip)``))); print "\n");
val _ = (print "bmsr_lookup1="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 1 (singleR 2 20 (Bin 2 1 10 (Bin 1 0 0 Tip Tip) Tip) Tip)``))); print "\n");
val _ = (print "bmsr_lookup2="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 2 (singleR 2 20 (Bin 2 1 10 (Bin 1 0 0 Tip Tip) Tip) Tip)``))); print "\n");
val _ = (print "bmsr_badsize="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 999 1 10 (Bin 1 0 0 Tip Tip) Tip)``))); print "\n");
