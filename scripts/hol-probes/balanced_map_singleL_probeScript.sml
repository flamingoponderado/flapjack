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
val structure_size_thm = prove (``!cmp t. invariant cmp t ==> size t = structure_size t``, Cases_on `t` >> rw [size_def,invariant_def,structure_size_def]);
val balanced_lem6 = prove (``!b b0 l.
    almost_balancedR l (b + b0 + 1) ∧
    b + b0 + 1 > delta * l ∧
    b < ratio * b0 ∧
    balanced b b0
   ⇒
    balanced (b + l + 1) b0 ∧ balanced l b``,
rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def, ratio_def]);
val singleL_thm = prove (``!k v l cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) n ∧
  ¬(size l + n ≤ 1) ∧
  n > delta * size l ∧
  size b < ratio * size b0 ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp l
  ⇒
  invariant cmp (singleL k v l (Bin n k' v' b b0)) ∧
  to_fmap cmp (singleL k v l (Bin n k' v' b b0)) =
    (to_fmap cmp l ⊌ to_fmap cmp (Bin n k' v' b b0)) |+ (key_set cmp k,v)``,
rw [singleL_def] >>
 Tactic.IMP_RES_TAC inv_props
 >- (fs [invariant_def, bin_def, size_def, structure_size_def, bin_def, key_ordered_def] >>
     Tactic.IMP_RES_TAC structure_size_thm >>
     gvs [size_def, key_ordered_to_fmap] >>
     full_simp_tac std_ss [ADD_ASSOC] >>
     Tactic.drule balanced_lem6 >> gvs [] >>
     metis_tac [to_fmap_key_set, cmp_thms, key_set_cmp_thm])
 >- (rw [to_fmap_def, bin_def, FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [to_fmap_def, invariant_def, key_ordered_def] >>
     rfs [key_ordered_to_fmap] >>
     full_simp_tac std_ss [FUNION_ASSOC] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms, FUPDATE_COMMUTES]));
val _ = if null(hyp singleL_thm) then () else raise Fail "open singleL hypotheses";
val _ = (print "bmsl_full="; Globals.show_types := true; print_thm singleL_thm; print "\n");
val _ = (print "bmsl_tree="; print_term(rand(concl(EVAL ``singleL 0 0 Tip (Bin 2 1 10 Tip (Bin 1 2 20 Tip Tip))``))); print "\n");
val _ = (print "bmsl_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (singleL 0 0 Tip (Bin 2 1 10 Tip (Bin 1 2 20 Tip Tip)))``))); print "\n");
val _ = (print "bmsl_lookup0="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 0 (singleL 0 0 Tip (Bin 2 1 10 Tip (Bin 1 2 20 Tip Tip)))``))); print "\n");
val _ = (print "bmsl_lookup1="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 1 (singleL 0 0 Tip (Bin 2 1 10 Tip (Bin 1 2 20 Tip Tip)))``))); print "\n");
val _ = (print "bmsl_lookup2="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 2 (singleL 0 0 Tip (Bin 2 1 10 Tip (Bin 1 2 20 Tip Tip)))``))); print "\n");
val _ = (print "bmsl_badsize="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 999 1 10 Tip (Bin 1 2 20 Tip Tip))``))); print "\n");
