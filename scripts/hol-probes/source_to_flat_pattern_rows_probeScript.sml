load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail label;
val _ = show_thm "pattern_bindings_typed=" source_to_flatProofTheory.pat_bindings_compile_pat;
val _ = show_thm "all_rows_typed=" source_to_flatProofTheory.can_pmatch_all_IMP_pmatch_rows;
