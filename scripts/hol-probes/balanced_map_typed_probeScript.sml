(* Typed source declarations for balanced_map (task 154). Free variables of a
   theorem conclusion are printed as a ∀* prefix; HOL stores them as
   implicitly universally quantified, so their order is not significant. *)
val _ = loadPath :=
  (Globals.HOLDIR ^ "/examples/data-structures/balanced_bst") ::
  !loadPath;
load "balanced_mapTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;

fun show label th =
  let val fvs = free_vars (concl th) in
    (print (label ^ "=");
     if null fvs then ()
     else (print "∀*";
           app (fn v =>
             let val ts = type_to_string (type_of v)
                 val ts = if String.sub (ts, 0) = #":"
                          then String.extract (ts, 1, NONE) else ts
             in print "("; print (#1 (dest_var v));
                print " :"; print ts; print ") " end) fvs;
           print ". ");
     app (fn h => (print_term h; print " ==> ")) (hyp th);
     print_term (concl th); print "\n")
  end;

val thy = "balanced_map";
val datatypeNames =
  List.map (fn n => String.substring (n, 0, String.size n - 6))
    (List.filter (fn n => String.isSuffix "_Axiom" n)
      (List.map #1 (DB.theorems thy)));

fun ctorsOf d =
  let
    fun try n =
      (TypeBase.constructors_of
         (mk_type (d, List.tabulate (n, fn _ => alpha)))
       handle _ => [])
    fun first [] = []
      | first (n :: ns) =
          let val cs = try n in if null cs then first ns else cs end
  in first [0, 1, 2, 3, 4] end;

val allCtors = List.concat (List.map ctorsOf datatypeNames);

fun emitDatatype label name =
  let val cs = ctorsOf name in
    if null cs then false
    else
      (print (label ^ "=");
       print (String.concatWith "; "
         (List.map (fn c =>
            let val (n, t) = dest_const c
            in n ^ ":" ^ type_to_string t end) cs));
       print "\n"; true)
  end;

fun ctorType name =
  case List.filter (fn c => #1 (dest_const c) = name) allCtors of
    [] => NONE
  | c :: _ => SOME (type_to_string (#2 (dest_const c)));

fun emit label name =
  case DB.lookup {Thy = thy, Name = name} of
    SOME (th, _) => show label th
  | NONE =>
      if emitDatatype label name then ()
      else case ctorType name of
        SOME s => (print (label ^ "="); print s; print "\n")
      | NONE => print (label ^ "=<not found in " ^ thy ^ ">\n");

(* local theorem: typed statement parse *)
val almost_balancedL_thm_statement =
  ``!l r.
    balanced l r
   ⇒
    almost_balancedL l r ∧ almost_balancedL (l + 1) r ∧
    almost_balancedL l (r - 1)``;
val _ = (print "almost_balancedL_thm_typed="; print_term almost_balancedL_thm_statement; print "\n");
(* local theorem: typed statement parse *)
val almost_balancedR_thm_statement =
  ``!l r.
    balanced l r
   ⇒
    almost_balancedR l r ∧ almost_balancedR l (r + 1) ∧
    almost_balancedR (l - 1) r``;
val _ = (print "almost_balancedR_thm_typed="; print_term almost_balancedR_thm_statement; print "\n");
val _ = emit "almost_balancedL_def_typed" "almost_balancedL_def";
val _ = emit "almost_balancedR_def_typed" "almost_balancedR_def";
(* local theorem: typed statement parse *)
val balanced_lem1_statement =
  ``!l r. l + r ≤ 1 ⇒ balanced l r``;
val _ = (print "balanced_lem1_typed="; print_term balanced_lem1_statement; print "\n");
(* local theorem: typed statement parse *)
val balanced_lem2_statement =
  ``!l r.
    ¬(l > delta * r) ∧
    almost_balancedL l r ∧
    ¬(l + r ≤ 1)
  ⇒
    balanced l r``;
val _ = (print "balanced_lem2_typed="; print_term balanced_lem2_statement; print "\n");
(* local theorem: typed statement parse *)
val balanced_lem3_statement =
  ``!b b0 r.
     almost_balancedL (b + b0 + 1) r ∧
     b + b0 + 1 > delta * r ∧
     b0 < ratio * b ∧
     balanced b b0
   ⇒
     balanced b (b0 + r + 1) ∧
     balanced b0 r``;
val _ = (print "balanced_lem3_typed="; print_term balanced_lem3_statement; print "\n");
(* local theorem: typed statement parse *)
val balanced_lem4_statement =
  ``!b b' b0' r.
  almost_balancedL (b + b' + b0' + 2) r ∧
  b + b' + b0' + 2 > delta * r ∧
  ¬(b' + b0' + 1 < ratio * b) ∧
  balanced b (b' + b0' + 1) ∧
  balanced b' b0'
  ⇒
  balanced (b + b' + 1) (b0' + r + 1) ∧
  balanced b b' ∧
  balanced b0' r``;
val _ = (print "balanced_lem4_typed="; print_term balanced_lem4_statement; print "\n");
(* local theorem: typed statement parse *)
val balanced_lem5_statement =
  ``!l r.
   ¬(r > delta * l) ∧ almost_balancedR l r
  ⇒
   balanced l r``;
val _ = (print "balanced_lem5_typed="; print_term balanced_lem5_statement; print "\n");
(* local theorem: typed statement parse *)
val balanced_lem6_statement =
  ``!b b0 l.
    almost_balancedR l (b + b0 + 1) ∧
    b + b0 + 1 > delta * l ∧
    b < ratio * b0 ∧
    balanced b b0
   ⇒
    balanced (b + l + 1) b0 ∧ balanced l b``;
val _ = (print "balanced_lem6_typed="; print_term balanced_lem6_statement; print "\n");
(* local theorem: typed statement parse *)
val balanced_lem7_statement =
  ``!b b0 b0' l b'.
    almost_balancedR l (b' + b0 + b0' + 2) ∧
    b' + b0 + b0' + 2 > delta * l ∧
    ¬(b' + b0' + 1 < ratio * b0) ∧
    balanced (b' + b0' + 1) b0 ∧
    balanced b' b0'
   ⇒
    balanced (b' + l + 1) (b0 + b0' + 1) ∧
    balanced l b' ∧
    balanced b0' b0``;
val _ = (print "balanced_lem7_typed="; print_term balanced_lem7_statement; print "\n");
val _ = emit "size_thm_typed" "size_thm";
(* local theorem: typed statement parse *)
val structure_size_to_fmap_statement =
  ``!cmp t. good_cmp cmp ∧ invariant cmp t ⇒
          FCARD (to_fmap cmp t) = structure_size t``;
val _ = (print "structure_size_to_fmap_typed="; print_term structure_size_to_fmap_statement; print "\n");
val _ = emit "balanced_map_typed" "balanced_map";
val _ = emit "bin_def_typed" "bin_def";
val _ = emit "delta_def_typed" "delta_def";
val _ = emit "empty_def_typed" "empty_def";
val _ = emit "lookup_def_typed" "lookup_def";
val _ = emit "member_def_typed" "member_def";
val _ = emit "null_def_typed" "null_def";
val _ = emit "ratio_def_typed" "ratio_def";
val _ = emit "singleton_def_typed" "singleton_def";
val _ = emit "size_def_typed" "size_def";
val _ = emit "to_fmap_key_set_typed" "to_fmap_key_set";
val _ = emit "insert_def_typed" "insert_def";
val _ = emit "insert_thm_typed" "insert_thm";
(* local theorem: typed statement parse *)
val inv_props_statement =
  ``!cmp s k v l r.
  good_cmp cmp ∧
  invariant cmp (Bin s k v l r)
  ⇒
  DISJOINT (FDOM (to_fmap cmp l)) (FDOM (to_fmap cmp r)) ∧
  (!x. key_set cmp x ∈ FDOM (to_fmap cmp l) ⇒ cmp k x = Greater) ∧
  (!x. key_set cmp x ∈ FDOM (to_fmap cmp r) ⇒ cmp k x = Less)``;
val _ = (print "inv_props_typed="; print_term inv_props_statement; print "\n");
val _ = emit "invariant_eq_typed" "invariant_eq";
val _ = emit "balanced_def_typed" "balanced_def";
val _ = emit "invariant_def_typed" "invariant_def";
val _ = emit "key_ordered_def_typed" "key_ordered_def";
val _ = emit "structure_size_def_typed" "structure_size_def";
(* local theorem: typed statement parse *)
val key_ordered_to_fmap_statement =
  ``!cmp k t res.
  good_cmp cmp ⇒
    (key_ordered cmp k t res
   ⇔
    ∀ks. ks ∈ FDOM (to_fmap cmp t) ⇒ key_set_cmp cmp k ks res)``;
val _ = (print "key_ordered_to_fmap_typed="; print_term key_ordered_to_fmap_statement; print "\n");
val _ = emit "key_set_cmp_def_typed" "key_set_cmp_def";
val _ = emit "key_set_cmp2_def_typed" "key_set_cmp2_def";
val _ = emit "key_set_cmp_thm_typed" "key_set_cmp_thm";
val _ = emit "key_set_eq_typed" "key_set_eq";
val _ = emit "key_set_equiv_typed" "key_set_equiv";
(* local theorem: typed statement parse *)
val key_set_nonempty_statement =
  ``good_cmp cmp ⇒ key_set cmp k ≠ {}``;
val _ = (print "key_set_nonempty_typed="; print_term key_set_nonempty_statement; print "\n");
val _ = emit "key_set_partition_typed" "key_set_partition";
val _ = emit "lookup_thm_typed" "lookup_thm";
(* local theorem: typed statement parse *)
val member_eq_lookup_statement =
  ``∀cmp k t. member cmp k t = IS_SOME (lookup cmp k t)``;
val _ = (print "member_eq_lookup_typed="; print_term member_eq_lookup_statement; print "\n");
val _ = emit "null_thm_typed" "null_thm";
val _ = emit "bal_def_typed" "bal_def";
val _ = emit "balL_def_typed" "balL_def";
val _ = emit "balR_def_typed" "balR_def";
val _ = emit "doubleL_def_typed" "doubleL_def";
val _ = emit "doubleR_def_typed" "doubleR_def";
val _ = emit "rotateL_def_typed" "rotateL_def";
val _ = emit "rotateR_def_typed" "rotateR_def";
val _ = emit "singleL_def_typed" "singleL_def";
val _ = emit "singleR_def_typed" "singleR_def";
(* local theorem: typed statement parse *)
val balanceL_balL_statement =
  ``!k v l r cmp.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  balanceL k v l r = balL k v l r``;
val _ = (print "balanceL_balL_typed="; print_term balanceL_balL_statement; print "\n");
(* local theorem: typed statement parse *)
val balanceL_thm_statement =
  ``!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k l Greater ∧
  key_ordered cmp k r Less ∧
  almost_balancedL (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (balanceL k v l r) ∧
  to_fmap cmp (balanceL k v l r) =
    (FUNION (to_fmap cmp l) (to_fmap cmp r)) |+ (key_set cmp k,v)``;
val _ = (print "balanceL_thm_typed="; print_term balanceL_thm_statement; print "\n");
(* local theorem: typed statement parse *)
val balanceR_balR_statement =
  ``!k v l r cmp.
  good_cmp cmp ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  balanceR k v l r = balR k v l r``;
val _ = (print "balanceR_balR_typed="; print_term balanceR_balR_statement; print "\n");
(* local theorem: typed statement parse *)
val balanceR_thm_statement =
  ``!k v l r cmp.
  good_cmp cmp ∧
  key_ordered cmp k r Less ∧
  key_ordered cmp k l Greater ∧
  almost_balancedR (size l) (size r) ∧
  invariant cmp l ∧
  invariant cmp r
  ⇒
  invariant cmp (balanceR k v l r) ∧
  to_fmap cmp (balanceR k v l r) =
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``;
val _ = (print "balanceR_thm_typed="; print_term balanceR_thm_statement; print "\n");
(* local theorem: typed statement parse *)
val doubleL_thm_statement =
  ``!k v l cmp n k' v' b b0.
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
    (to_fmap cmp l ⊌ to_fmap cmp (Bin n k' v' b b0)) |+ (key_set cmp k,v)``;
val _ = (print "doubleL_thm_typed="; print_term doubleL_thm_statement; print "\n");
(* local theorem: typed statement parse *)
val doubleR_thm_statement =
  ``!k v r cmp n k' v' b b0.
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
    (to_fmap cmp (Bin n k' v' b b0) ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``;
val _ = (print "doubleR_thm_typed="; print_term doubleR_thm_statement; print "\n");
(* local theorem: typed statement parse *)
val rotateL_thm_statement =
  ``!k v l r cmp.
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
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``;
val _ = (print "rotateL_thm_typed="; print_term rotateL_thm_statement; print "\n");
(* local theorem: typed statement parse *)
val rotateR_thm_statement =
  ``!k v l r cmp.
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
    (to_fmap cmp l ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``;
val _ = (print "rotateR_thm_typed="; print_term rotateR_thm_statement; print "\n");
(* local theorem: typed statement parse *)
val singleL_thm_statement =
  ``!k v l cmp n k' v' b b0.
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
    (to_fmap cmp l ⊌ to_fmap cmp (Bin n k' v' b b0)) |+ (key_set cmp k,v)``;
val _ = (print "singleL_thm_typed="; print_term singleL_thm_statement; print "\n");
(* local theorem: typed statement parse *)
val singleR_thm_statement =
  ``!k v r cmp n k' v' b b0.
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
    (to_fmap cmp (Bin n k' v' b b0) ⊌ to_fmap cmp r) |+ (key_set cmp k,v)``;
val _ = (print "singleR_thm_typed="; print_term singleR_thm_statement; print "\n");
val _ = emit "balanceL_def_typed" "balanceL_def";
val _ = emit "balanceR_def_typed" "balanceR_def";
val _ = emit "key_set_def_typed" "key_set_def";
val _ = emit "to_fmap_def_typed" "to_fmap_def";
(* local theorem: typed statement parse *)
val structure_size_thm_statement =
  ``!cmp t. invariant cmp t ⇒ size t = structure_size t``;
val _ = (print "structure_size_thm_typed="; print_term structure_size_thm_statement; print "\n");

val _ = OS.Process.exit OS.Process.success;
