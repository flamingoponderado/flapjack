load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse Tactic Rewrite simpLib bossLib Tactical BasicProvers arithmeticTheory comparisonTheory pred_setTheory finite_mapTheory balanced_mapTheory;
val _ = Globals.linewidth := 10000;
val FCARD_DISJOINT_UNION = prove (``!m1 m2.
    DISJOINT (FDOM m1) (FDOM m2) ∨ DISJOINT (FDOM m2) (FDOM m1)
  ⇒ FCARD (FUNION m1 m2) = FCARD m1 + FCARD m2``,
 rw [DISJOINT_DEF, FCARD_DEF] >>
 metis_tac [CARD_UNION, FDOM_FINITE, CARD_DEF, ADD_0, INTER_COMM]);
val _ = if null(hyp FCARD_DISJOINT_UNION) then () else raise Fail "open union theorem";
val structure_size_thm = prove (``!cmp t. invariant cmp t ⇒ size t = structure_size t``,
 Cases_on `t` >>
 rw [size_def, invariant_def, structure_size_def]);
val _ = if null(hyp structure_size_thm) then () else raise Fail "open cardinality theorem";
val _ = (print "structure_size_thm="; Globals.show_types := true; print_thm structure_size_thm; print "\n");
val structure_size_to_fmap = prove (``!cmp t. good_cmp cmp ∧ invariant cmp t ⇒
          FCARD (to_fmap cmp t) = structure_size t``,
 Induct_on `t` >>
 rw [invariant_eq, structure_size_def, to_fmap_def, FCARD_FEMPTY] >>
 rw [FCARD_FUPDATE, FCARD_DISJOINT_UNION]);
val _ = if null(hyp structure_size_to_fmap) then () else raise Fail "open cardinality theorem";
val _ = (print "structure_size_to_fmap="; Globals.show_types := true; print_thm structure_size_to_fmap; print "\n");
val size_thm = prove (``!cmp t. good_cmp cmp ∧ invariant cmp t ⇒ size t = FCARD (to_fmap cmp t)``,
 metis_tac [structure_size_thm, structure_size_to_fmap]);
val _ = if null(hyp size_thm) then () else raise Fail "open cardinality theorem";
val _ = (print "size_thm="; Globals.show_types := true; print_thm size_thm; print "\n");
val _ = (print "bmcard_empty_size="; print_term(rand(concl(EVAL ``size ((Tip:(num,num)balanced_map))``))); print "\n");
val _ = (print "bmcard_empty_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) ((Tip:(num,num)balanced_map))``))); print "\n");
val _ = (print "bmcard_singleton_size="; print_term(rand(concl(EVAL ``size (Bin 1 3 30 Tip Tip)``))); print "\n");
val _ = (print "bmcard_singleton_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 1 3 30 Tip Tip)``))); print "\n");
val _ = (print "bmcard_left_size="; print_term(rand(concl(EVAL ``size (Bin 2 3 30 (Bin 1 1 10 Tip Tip) Tip)``))); print "\n");
val _ = (print "bmcard_left_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 2 3 30 (Bin 1 1 10 Tip Tip) Tip)``))); print "\n");
val _ = (print "bmcard_right_size="; print_term(rand(concl(EVAL ``size (Bin 2 3 30 Tip (Bin 1 5 50 Tip Tip))``))); print "\n");
val _ = (print "bmcard_right_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 2 3 30 Tip (Bin 1 5 50 Tip Tip))``))); print "\n");
val _ = (print "bmcard_both_size="; print_term(rand(concl(EVAL ``size (Bin 3 3 30 (Bin 1 1 10 Tip Tip) (Bin 1 5 50 Tip Tip))``))); print "\n");
val _ = (print "bmcard_both_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. if x < y then Less else if x = y then Equal else Greater) (Bin 3 3 30 (Bin 1 1 10 Tip Tip) (Bin 1 5 50 Tip Tip))``))); print "\n");
val _ = (print "bmcard_equivalent_invariant="; print_term(rand(concl(EVAL ``invariant (\x:num y:num. Equal) (Bin 1 3 30 Tip Tip)``))); print "\n");
