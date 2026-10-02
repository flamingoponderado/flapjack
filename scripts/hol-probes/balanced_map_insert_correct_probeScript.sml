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
val rotateL_thm = prove (``!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k r Less ∧
  key_ordered cmp k l Greater ∧
  ¬(size l + size r ≤ 1) ∧
  size r > delta * size l ∧
  almost_balancedR (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (rotateL k v l r) ∧
  to_fmap cmp (rotateL k v l r) =
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``,
Cases_on `r`
 >- fs [size_def] >>
 rw [size_def, rotateL_def] >>
 metis_tac [singleL_thm, doubleL_thm, ADD_COMM, NOT_ZERO_LT_ZERO, GREATER_DEF]);
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
val balanced_lem1 = prove (``!l r. l + r ≤ 1 ⇒ balanced l r``,
rw [balanced_def]);
val balanced_lem5 = prove (``!l r.
   ¬(r > delta * l) ∧ almost_balancedR l r
  ⇒
   balanced l r``,
rw [almost_balancedR_def, balanced_def, NOT_LESS_EQUAL, NOT_GREATER,
          TIMES_MIN, delta_def]);
val balanceR_thm = prove (``!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k r Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (balanceR k v l r) ∧
  to_fmap cmp (balanceR k v l r) =
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``,
rw [] >>
 `balanceR k v l r = balR k v l r` by metis_tac [balanceR_balR] >>
 rw [balR_def, invariant_def] >>
 Tactic.IMP_RES_TAC structure_size_thm >>
 rw [balanced_lem1, balanced_lem5, to_fmap_def] >>
 metis_tac [rotateL_thm]);
val _ = if null(hyp balanceR_thm) then () else raise Fail "open balanceR correctness hypotheses";

open Tactic Rewrite boolSyntax boolTheory Drule;
val _ = bossLib.augment_srw_ss [rewrites
  [FUNION_FUPDATE_1,FUNION_ASSOC,FUNION_FEMPTY_2,FUNION_FEMPTY_1,FDOM_DRESTRICT,
   DRESTRICT_UNIV]]

fun fs x = full_simp_tac (srw_ss()++ARITH_ss) x;
fun rfs x = REV_FULL_SIMP_TAC (srw_ss()++ARITH_ss) x;
val rw = srw_tac [ARITH_ss];

val fmrw = srw_tac [ARITH_ss, rewrites [FLOOKUP_UPDATE,FLOOKUP_FUNION,FLOOKUP_DRESTRICT,
                    FUNION_FUPDATE_2,FAPPLY_FUPDATE_THM,FUNION_DEF, DRESTRICT_DEF]];

fun inv_to_front_tac tm (g as (asl,w)) = let
  val tms = strip_conj w
  val (tms1,tms2) = List.partition (fn x => can (find_term (can (match_term tm))) x) tms
  val tms = tms1@tms2
  val thm = prove (``^w ⇔ ^(list_mk_conj tms)``, SIMP_TAC (std_ss) [AC CONJ_COMM CONJ_ASSOC])
in
  ONCE_REWRITE_TAC [thm] g
end

val inv_mp_tac = let
  val lemma = PROVE [] ``!A B C D. (A ⇒ B ∧ C) ⇒ (A ∧ (B ∧ C ⇒  D)) ⇒ (B ∧ D)``
in
  fn th => fn (g as (asl,w)) => let
    val c = th |> concl
    val (xs,b) = strip_forall c
    val tm = b |> dest_imp |> snd |> strip_conj |> hd
    val tm2 = hd (strip_conj w)
    val s = fst (match_term tm tm2)
    val th2 = SPECL (map (Term.subst s) xs) th
    val th3 = MATCH_MP lemma th2
  in
    MATCH_MP_TAC (GEN_ALL th3) g
  end
end

val almost_balancedL_thm = prove (``!l r.
    balanced l r
   ⇒
    almost_balancedL l r ∧ almost_balancedL (l + 1) r ∧
    almost_balancedL l (r - 1)``,
 rw [almost_balancedL_def, balanced_def, TIMES_MIN, delta_def] >>
 rw [MIN_DEF]);
val _ = if null(hyp almost_balancedL_thm) then () else raise Fail "open almost-balance";
val almost_balancedR_thm = prove (``!l r.
    balanced l r
   ⇒
    almost_balancedR l r ∧ almost_balancedR l (r + 1) ∧
    almost_balancedR (l - 1) r``,
 rw [almost_balancedR_def, balanced_def, TIMES_MIN, delta_def] >>
 rw [MIN_DEF]);
val _ = if null(hyp almost_balancedR_thm) then () else raise Fail "open almost-balance";
val insert_thm_replay = prove (``∀t.
  good_cmp cmp ∧
  invariant cmp t
  ⇒
  invariant cmp (insert cmp k v t) ∧
  to_fmap cmp (insert cmp k v t) = to_fmap cmp t |+ (key_set cmp k,v)``,
 Induct_on `t`
 >- fs [insert_def, singleton_def, to_fmap_def, invariant_eq,
        structure_size_def, balanced_def, size_def, key_ordered_def] >>
 simp [invariant_eq] >>
 rpt gen_tac >>
 strip_tac >>
 fs [insert_def] >>
 Cases_on `cmp k k'` >>
 fs [] >>
 simp [] >>
 TRY (inv_mp_tac balanceL_thm) >>
 TRY (inv_mp_tac balanceR_thm) >>
 conj_asm1_tac >>
 rw [to_fmap_def]
 >- (rfs [key_ordered_to_fmap] >>
     rw [] >>
     imp_res_tac to_fmap_key_set >>
     rw [key_set_cmp_thm] >>
     metis_tac [cmp_thms])
 >- (imp_res_tac size_thm >>
     rw [FCARD_FUPDATE] >>
     fs [key_ordered_to_fmap] >>
     metis_tac [almost_balancedL_thm])
 >- (rfs [key_ordered_to_fmap] >>
     rw [] >>
     `key_set cmp k ≠ key_set cmp k'` by metis_tac [key_set_eq, cmp_thms] >>
     metis_tac [FUPDATE_COMMUTES])
 >- (fs [invariant_def] >>
     rfs [key_ordered_to_fmap] >>
     metis_tac [to_fmap_key_set, key_set_cmp_thm, cmp_thms])
 >- metis_tac [key_set_eq, FUPDATE_EQ]
 >- (rfs [key_ordered_to_fmap] >>
     rw [] >>
     imp_res_tac to_fmap_key_set >>
     rw [key_set_cmp_thm] >>
     metis_tac [cmp_thms])
 >- (imp_res_tac size_thm >>
     rw [FCARD_FUPDATE] >>
     fs [key_ordered_to_fmap] >>
     metis_tac [almost_balancedR_thm])
 >- (rw [FUNION_FUPDATE_2, to_fmap_def] >>
     rfs [key_ordered_to_fmap] >>
     rw [] >>
     metis_tac [FUPDATE_COMMUTES, cmp_thms, to_fmap_key_set, key_set_cmp_thm]));
val _ = if null(hyp insert_thm_replay) then () else raise Fail "open insert proof";
val _ = (print "insert_thm="; Globals.show_types := true; print_thm insert_thm_replay; print "\n");
val _ = (print "bminsert_tip_tree="; print_term(rand(concl(EVAL ``(insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 3 31 (Tip:(num,num)balanced_map))``))); print "\n");
val _ = (print "bminsert_tip_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 3 31 (Tip:(num,num)balanced_map))``))); print "\n");
val _ = (print "bminsert_tip_lookup="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 3 (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 3 31 (Tip:(num,num)balanced_map))``))); print "\n");
val _ = (print "bminsert_less_tree="; print_term(rand(concl(EVAL ``(insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 1 11 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_less_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 1 11 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_less_lookup="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 1 (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 1 11 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_equal_tree="; print_term(rand(concl(EVAL ``(insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 3 31 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_equal_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 3 31 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_equal_lookup="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 3 (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 3 31 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_greater_tree="; print_term(rand(concl(EVAL ``(insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 51 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_greater_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 51 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_greater_lookup="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 5 51 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_rotate_right_tree="; print_term(rand(concl(EVAL ``(insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 0 1 (Bin 2 3 30 (Bin 1 1 10 Tip Tip) Tip))``))); print "\n");
val _ = (print "bminsert_rotate_right_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 0 1 (Bin 2 3 30 (Bin 1 1 10 Tip Tip) Tip))``))); print "\n");
val _ = (print "bminsert_rotate_right_lookup="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 0 (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 0 1 (Bin 2 3 30 (Bin 1 1 10 Tip Tip) Tip))``))); print "\n");
val _ = (print "bminsert_rotate_left_tree="; print_term(rand(concl(EVAL ``(insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 6 61 (Bin 2 3 30 Tip (Bin 1 5 50 Tip Tip)))``))); print "\n");
val _ = (print "bminsert_rotate_left_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 6 61 (Bin 2 3 30 Tip (Bin 1 5 50 Tip Tip)))``))); print "\n");
val _ = (print "bminsert_rotate_left_lookup="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 6 (insert (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) 6 61 (Bin 2 3 30 Tip (Bin 1 5 50 Tip Tip)))``))); print "\n");
val _ = (print "bminsert_equivalent_tree="; print_term(rand(concl(EVAL ``(insert (\x:num y:num. Equal) 2 99 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_equivalent_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. Equal) (insert (\x:num y:num. Equal) 2 99 (Bin 1 3 30 Tip Tip))``))); print "\n");
val _ = (print "bminsert_equivalent_lookup="; print_term(rand(concl(EVAL ``lookup (\x:num y:num. Equal) 2 (insert (\x:num y:num. Equal) 2 99 (Bin 1 3 30 Tip Tip))``))); print "\n");
