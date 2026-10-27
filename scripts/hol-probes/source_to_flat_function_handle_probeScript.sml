load "source_to_flatProofTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
fun show_thm label th =
  if null (hyp th) then (print label; Lib.with_flag (Globals.show_types,true) print_term (concl th); print "\n")
  else raise Fail label;
val fun_compile = prove(``source_to_flat$compile_exp t env (ast$Fun x e) =
  flatLang$Fun (source_to_flat$join_all_names t) x
    (source_to_flat$compile_exp t (env with v := nsBind x (Local None x) env.v) e)``,
  simp [source_to_flatTheory.compile_exp_def]);
val _ = show_thm "function_compile_typed=" fun_compile;
val _ = show_thm "empty_match_typed=" (hd (CONJUNCTS evaluateTheory.evaluate_match_def));
val _ = show_thm "flat_rows_typed=" flatSemTheory.pmatch_rows_def;
