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
val doubleR_thm = prove (``!k v r cmp n k' v' b b0.
  good_cmp cmp ∧
  key_ordered cmp k (Bin n k' v' b b0) Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL n (size r) ∧
  ¬(size r + n ≤ 1) ∧
  n > delta * size r ∧
  ¬(size b0 < ratio * size b) ∧
  invariant cmp (Bin n k' v' b b0) ∧
  invariant cmp r
 ⇒
  invariant cmp (doubleR k v (Bin n k' v' b b0) r) ∧
  to_fmap cmp (doubleR k v (Bin n k' v' b b0) r) =
    (to_fmap cmp (Bin n k' v' b b0) ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``,
 rw [] >>
 `structure_size b0 ≠ 0`
          by (fs [delta_def, ratio_def, invariant_def, size_def,
                  NOT_LESS_EQUAL, NOT_LESS, NOT_GREATER] >>
              Tactic.IMP_RES_TAC structure_size_thm >>
              fs []) >>
 Cases_on `b0` >>
 fs [structure_size_def, doubleR_def, bin_def] >>
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
     \\ drule balanced_lem4
     \\ asm_simp_tac std_ss [ADD_ASSOC])
 >- (rw [FUNION_FUPDATE_2, FUNION_FUPDATE_1] >>
     fs [key_ordered_def] >>
     rfs [key_ordered_to_fmap]
     >- (res_tac \\ drule_all good_cmp_greater_antisym \\ rewrite_tac [])
     >- (res_tac \\ drule_all good_cmp_greater_antisym \\ rewrite_tac []) >>
     `key_set cmp k' ≠ key_set cmp k'' ∧
      key_set cmp k ≠ key_set cmp k' ∧
      key_set cmp k ≠ key_set cmp k''` by
       (drule_then (rewrite_tac o single) key_set_eq
        \\ Tactic.CCONTR_TAC \\ rfs [])
     \\ simp_tac std_ss [FUNION_ASSOC]
     \\ metis_tac [FUPDATE_COMMUTES]));

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

val rotateR_thm = prove (``!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  ¬(size l + size r ≤ 1) ∧
  size l > delta * size r ∧
  almost_balancedL (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (rotateR k v l r) ∧
  to_fmap cmp (rotateR k v l r) =
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``,
  Cases_on `l`
  >- fs [size_def] >>
  rw [size_def, rotateR_def] >>
  metis_tac [singleR_thm, doubleR_thm, ADD_COMM, NOT_ZERO_LT_ZERO, GREATER_DEF]);

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

val balanced_lem1 = prove (``!l r. l + r ≤ 1 ⇒ balanced l r``, rw [balanced_def]);

val balanced_lem2 = prove (``!l r.
    ¬(l > delta * r) ∧
    almost_balancedL l r ∧
    ¬(l + r ≤ 1)
  ⇒
    balanced l r``, rw [almost_balancedL_def, balanced_def, NOT_LESS_EQUAL, NOT_GREATER,
          TIMES_MIN, delta_def]);

val balanceL_thm = prove (``!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (balanceL k v l r) ∧
  to_fmap cmp (balanceL k v l r) =
    (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v)``,
 rw [] >>
 `balanceL k v l r = balL k v l r` by metis_tac [balanceL_balL] >>
 rw [] >>
 rw [balL_def, invariant_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 rw [balanced_lem1, balanced_lem2, to_fmap_def] >>
 metis_tac [rotateR_thm]);
val _ = if null(hyp balanceL_thm) then () else raise Fail "open balanceL theorem hypotheses";
val _ = (print "bmlc_full="; Globals.show_types := true; print_thm balanceL_thm; print "\n");
val _ = (print "bmlc_empty_tree="; print_term(rand(concl(EVAL ``balanceL 5 50 Tip Tip``))); print "\n");
val _ = (print "bmlc_empty_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (balanceL 5 50 Tip Tip)``))); print "\n");
val _ = (print "bmlc_empty_lookup5="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 (balanceL 5 50 Tip Tip)``))); print "\n");
val _ = (print "bmlc_fallback_tree="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 1 0 0 Tip Tip) (Bin 1 6 6 Tip Tip)``))); print "\n");
val _ = (print "bmlc_fallback_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (balanceL 5 50 (Bin 1 0 0 Tip Tip) (Bin 1 6 6 Tip Tip))``))); print "\n");
val _ = (print "bmlc_fallback_lookup5="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 (balanceL 5 50 (Bin 1 0 0 Tip Tip) (Bin 1 6 6 Tip Tip))``))); print "\n");
val _ = (print "bmlc_single_tip_tree="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 3 1 1 (Bin 1 0 0 Tip Tip) (Bin 1 2 2 Tip Tip)) Tip``))); print "\n");
val _ = (print "bmlc_single_tip_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (balanceL 5 50 (Bin 3 1 1 (Bin 1 0 0 Tip Tip) (Bin 1 2 2 Tip Tip)) Tip)``))); print "\n");
val _ = (print "bmlc_single_tip_lookup5="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 (balanceL 5 50 (Bin 3 1 1 (Bin 1 0 0 Tip Tip) (Bin 1 2 2 Tip Tip)) Tip)``))); print "\n");
val _ = (print "bmlc_double_tip_tree="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) Tip``))); print "\n");
val _ = (print "bmlc_double_tip_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (balanceL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) Tip)``))); print "\n");
val _ = (print "bmlc_double_tip_lookup5="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 (balanceL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) Tip)``))); print "\n");
val _ = (print "bmlc_heavy_single_tree="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 4 2 2 (Bin 2 1 1 (Bin 1 0 0 Tip Tip) Tip) (Bin 1 3 3 Tip Tip)) (Bin 1 6 6 Tip Tip)``))); print "\n");
val _ = (print "bmlc_heavy_single_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (balanceL 5 50 (Bin 4 2 2 (Bin 2 1 1 (Bin 1 0 0 Tip Tip) Tip) (Bin 1 3 3 Tip Tip)) (Bin 1 6 6 Tip Tip))``))); print "\n");
val _ = (print "bmlc_heavy_single_lookup5="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 (balanceL 5 50 (Bin 4 2 2 (Bin 2 1 1 (Bin 1 0 0 Tip Tip) Tip) (Bin 1 3 3 Tip Tip)) (Bin 1 6 6 Tip Tip))``))); print "\n");
val _ = (print "bmlc_heavy_double_tree="; print_term(rand(concl(EVAL ``balanceL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) (Bin 1 6 6 Tip Tip)``))); print "\n");
val _ = (print "bmlc_heavy_double_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (balanceL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) (Bin 1 6 6 Tip Tip))``))); print "\n");
val _ = (print "bmlc_heavy_double_lookup5="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 (balanceL 5 50 (Bin 4 1 1 (Bin 1 0 0 Tip Tip) (Bin 2 2 2 Tip (Bin 1 3 3 Tip Tip))) (Bin 1 6 6 Tip Tip))``))); print "\n");
