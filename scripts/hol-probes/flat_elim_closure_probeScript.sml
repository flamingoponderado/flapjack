load "flat_elimTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show_thm label th =
  if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_thm "closure_definition=" spt_closureTheory.closure_spt_def;
val _ = show_thm "tree_union_definition=" spt_closureTheory.num_set_tree_union_def;
val _ = show_thm "analyse_exp_definition=" flat_elimTheory.analyse_exp_def;
val _ = show_thm "analysis_union_definition=" flat_elimTheory.code_analysis_union_def;
val _ = show_thm "analyse_code_definition=" flat_elimTheory.analyse_code_def;
val _ = show_thm "remove_unreachable_definition=" flat_elimTheory.remove_unreachable_def;
val _ = show_thm "has_eval_dec_definition=" flat_elimTheory.has_Eval_dec_def;
val _ = show_thm "remove_flat_prog_definition=" flat_elimTheory.remove_flat_prog_def;
val _ = show_eval "analysis_union_nat=" ``flat_elim$code_analysis_union
  (sptree$LS 7n, sptree$LN) (sptree$LS 9n, sptree$LN)``;
val _ = show_eval "analysis_union_bool=" ``flat_elim$code_analysis_union
  (sptree$LS T, sptree$LN) (sptree$LS F, sptree$LN)``;
val _ = show_eval "remove_unreachable_nat=" ``flat_elim$remove_unreachable
  (sptree$LS 7n) [flatLang$Lit backend_common$None (ast$IntLit 1)]``;
val _ = show_eval "remove_unreachable_bool=" ``flat_elim$remove_unreachable
  (sptree$LS T) [flatLang$Lit backend_common$None (ast$IntLit 1)]``;
val _ = show_eval "remove_unreachable_nat_live=" ``flat_elim$remove_unreachable
  (sptree$LS 7n) [flatLang$App backend_common$None (flatLang$GlobalVarInit 0)
    [flatLang$Lit backend_common$None (ast$IntLit 1)]]``;
val _ = show_eval "remove_unreachable_bool_live=" ``flat_elim$remove_unreachable
  (sptree$LS T) [flatLang$App backend_common$None (flatLang$GlobalVarInit 0)
    [flatLang$Lit backend_common$None (ast$IntLit 1)]]``;
val _ = show_thm "fold_domain=" spt_closureTheory.domain_spt_fold_union;
val _ = show_thm "adjacent=" spt_closureTheory.is_adjacent_def;
val _ = show_thm "reachable=" spt_closureTheory.is_reachable_def;
val _ = show_thm "closure_reachable=" spt_closureTheory.closure_spt_thm;
val _ = show_thm "tree_union_lookup=" spt_closureTheory.lookup_num_set_tree_union;
val _ = show_thm "tree_union_symmetric=" spt_closureTheory.num_set_tree_union_sym;
val _ = show_thm "adjacent_union=" spt_closureTheory.is_adjacent_num_set_tree_union;
val _ = show_thm "reachable_union=" spt_closureTheory.is_reachable_num_set_tree_union;
val _ = show_eval "noncanonical_subset=" ``sptree$subspt (sptree$BN sptree$LN sptree$LN : unit sptree$spt) (sptree$LS ())``;
val _ = show_eval "noncanonical_closure=" ``spt_closure$closure_spt (sptree$LS ()) (sptree$LS (sptree$BN sptree$LN sptree$LN : unit sptree$spt))``;
