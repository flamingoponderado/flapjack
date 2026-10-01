load "bossLib";
load "preamble";
load "word_allocProofTheory";
open bossLib HolKernel Parse preamble word_allocProofTheory reg_allocTheory sptreeTheory;
fun print_eval label q = let val th = SIMP_CONV (srw_ss())
  [even_starting_locals_def,domain_fromAList,is_phy_var_def,DISJ_IMP_THM,FORALL_AND_THM] q in
 (print (label ^ "="); print_term (rconc th); print "\n") end;
print_eval "wa_even_empty" ``even_starting_locals (fromAList ([]:(num # word64 wordLang$word_loc) list))``;
print_eval "wa_even_zero" ``even_starting_locals (fromAList [(0,Word (0w:word64))])``;
print_eval "wa_even_even_holes" ``even_starting_locals (fromAList [(0,Word (1w:word64));(8,Loc 7 9);(64,Word 3w)])``;
print_eval "wa_even_odd" ``even_starting_locals (fromAList [(3,Word (0w:word64))])``;
print_eval "wa_even_mixed" ``even_starting_locals (fromAList [(2,Loc 0 0);(5,Word (0w:word64))])``;
print_eval "wa_even_overwrite" ``even_starting_locals (fromAList [(8,Word (7w:word64));(8,Loc 2 3)])``;
