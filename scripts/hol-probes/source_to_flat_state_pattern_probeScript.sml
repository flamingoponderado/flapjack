load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show_thm "store_rel_rules=" source_to_flatProofTheory.sv_rel_rules;
val _ = show_thm "state_rel_rules=" source_to_flatProofTheory.s_rel_rules;
val _ = show_thm "state_rel_cases=" source_to_flatProofTheory.s_rel_cases;
val _ = show_thm "match_result_def=" source_to_flatProofTheory.match_result_rel_def;
val _ = show_thm "match_result_imp=" source_to_flatProofTheory.match_result_rel_imp;
val _ = show_thm "store_same_type=" semanticPrimitivesTheory.store_v_same_type_def;
val _ = show_thm "store_assign=" semanticPrimitivesTheory.store_assign_def;
val _ = show_thm "store_alloc=" semanticPrimitivesTheory.store_alloc_def;
fun show_eval label tm = (print label; print_term (rhs (concl (EVAL tm))); print "\n");
val _ = show_eval "allocate_ref=" ``semanticPrimitives$store_alloc (Refv (semanticPrimitives$Litv (IntLit 5))) []``;
val _ = show_eval "assign_ref=" ``semanticPrimitives$store_assign 0 (Refv (semanticPrimitives$Litv (IntLit 9))) [Refv (semanticPrimitives$Litv (IntLit 5))]``;
val _ = show_eval "assign_wrong_type=" ``semanticPrimitives$store_assign 0 (W8array [3w]) [Refv (semanticPrimitives$Litv (IntLit 5))]``;
val _ = show_eval "assign_missing=" ``semanticPrimitives$store_assign 1 (Refv (semanticPrimitives$Litv (IntLit 9))) [Refv (semanticPrimitives$Litv (IntLit 5))]``;
