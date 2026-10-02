load "bossLib";
load "balanced_mapTheory";
open HolKernel Parse bossLib Tactical BasicProvers balanced_mapTheory;
val _ = Globals.show_types := true;
val _ = Globals.linewidth := 10000;
val member_eq_lookup = prove (``!cmp k t. member cmp k t = IS_SOME (lookup cmp k t)``,
  Induct_on `t` >> gvs [member_def,lookup_def] >> rpt Tactic.GEN_TAC >> CASE_TAC >> gvs []);
val _ = if null(hyp member_eq_lookup) then () else raise Fail "open membership hypotheses";
val _ = (print "bmm_theorem="; print_thm member_eq_lookup; print "\n");
val _ = (print "bmm_nil="; print_term (boolSyntax.rhs(concl(EVAL ``member (\(q:bool) (k:num). Equal) T (Tip:(num,num)balanced_map)``))); print "\n");
val _ = (print "bmm_root="; print_term (boolSyntax.rhs(concl(EVAL ``member (\(q:bool) (k:num). Equal) F (Bin 0 7 99 Tip Tip)``))); print "\n");
val _ = (print "bmm_left_absent="; print_term (boolSyntax.rhs(concl(EVAL ``member (\(q:bool) (k:num). Less) F (Bin 0 7 99 Tip Tip)``))); print "\n");
val _ = (print "bmm_right_absent="; print_term (boolSyntax.rhs(concl(EVAL ``member (\(q:bool) (k:num). Greater) F (Bin 0 7 99 Tip Tip)``))); print "\n");
val _ = (print "bmm_left_present="; print_term (boolSyntax.rhs(concl(EVAL ``member (\(q:bool) (k:num). if k = 7 then Less else Equal) T (Bin 0 7 99 (Bin 999 8 22 Tip Tip) Tip)``))); print "\n");
val _ = (print "bmm_right_present="; print_term (boolSyntax.rhs(concl(EVAL ``member (\(q:bool) (k:num). if k = 7 then Greater else Equal) F (Bin 0 7 99 Tip (Bin 999 8 22 Tip Tip))``))); print "\n");
