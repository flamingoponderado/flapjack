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
val balanced_lem7 = prove (``!b b0 b0' l b'.
    almost_balancedR l (b' + b0 + b0' + 2) ∧
    b' + b0 + b0' + 2 > delta * l ∧
    ¬(b' + b0' + 1 < ratio * b0) ∧
    balanced (b' + b0' + 1) b0 ∧
    balanced b' b0'
   ⇒
    balanced (b' + l + 1) (b0 + b0' + 1) ∧
    balanced l b' ∧
    balanced b0' b0``,
rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def, ratio_def]);
val doubleL_thm = prove (``!k v l cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) n ∧
  ¬(n + size l ≤ 1) ∧
  n > delta * size l ∧
  ¬(size b < ratio * size b0) ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp l
  ⇒
  invariant cmp (doubleL k v l (Bin n k' v' b b0)) ∧
  to_fmap cmp (doubleL k v l (Bin n k' v' b b0)) =
    (to_fmap cmp l ⊌ to_fmap cmp (Bin n k' v' b b0)) |+ (key_set cmp k,v)``,
rw [] >>
 `structure_size b ≠ 0`
          by (fs [delta_def, ratio_def, invariant_def, size_def,
                  NOT_LESS_EQUAL, NOT_LESS, NOT_GREATER] >>
              Tactic.IMP_RES_TAC structure_size_thm >>
              fs []) >>
 Cases_on `b` >>
 fs [structure_size_def, doubleL_def, bin_def] >>
 Tactic.IMP_RES_TAC inv_props >>
 fs [BoundedRewrites.Once invariant_def] >>
 Tactic.IMP_RES_TAC inv_props >>
 fs [invariant_def, to_fmap_def]
 >- (fs [size_def, bin_def, to_fmap_def] >>
     Tactic.IMP_RES_TAC structure_size_thm >>
     simp [structure_size_def, key_ordered_def] >>
     fs [structure_size_def, to_fmap_def, key_ordered_def] >>
     rfs [key_ordered_to_fmap] >>
     rw []
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     \\ full_simp_tac std_ss [ADD_ASSOC]
     \\ Tactic.drule balanced_lem7
     \\ asm_simp_tac std_ss [ADD_ASSOC])
 >- (rw [FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [key_ordered_def] >>
     rfs [key_ordered_to_fmap]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [cmp_thms]
     >- metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms] >>
     `key_set cmp k' ≠ key_set cmp k'' ∧
      key_set cmp k ≠ key_set cmp k' ∧
      key_set cmp k ≠ key_set cmp k''` by
       (Tactic.drule_then (Rewrite.REWRITE_TAC o single) key_set_eq
        \\ Tactic.CCONTR_TAC \\ rfs [])
     \\ simp_tac std_ss [FUNION_ASSOC]
     \\ metis_tac [FUPDATE_COMMUTES]));
val _ = if null(hyp doubleL_thm) then () else raise Fail "open doubleL hypotheses";
val _ = (print "bmdl_full="; Globals.show_types := true; print_thm doubleL_thm; print "\n");
val _ = (print "bmdl_tree="; print_term(rand(concl(EVAL ``doubleL 0 0 Tip (Bin 2 2 20 (Bin 1 1 10 Tip Tip) Tip)``))); print "\n");
val _ = (print "bmdl_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (doubleL 0 0 Tip (Bin 2 2 20 (Bin 1 1 10 Tip Tip) Tip))``))); print "\n");
val _ = (print "bmdl_lookup0="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 0 (doubleL 0 0 Tip (Bin 2 2 20 (Bin 1 1 10 Tip Tip) Tip))``))); print "\n");
val _ = (print "bmdl_lookup1="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 1 (doubleL 0 0 Tip (Bin 2 2 20 (Bin 1 1 10 Tip Tip) Tip))``))); print "\n");
val _ = (print "bmdl_lookup2="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 2 (doubleL 0 0 Tip (Bin 2 2 20 (Bin 1 1 10 Tip Tip) Tip))``))); print "\n");
val _ = (print "bmdl_badsize="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 999 2 20 (Bin 1 1 10 Tip Tip) Tip)``))); print "\n");
