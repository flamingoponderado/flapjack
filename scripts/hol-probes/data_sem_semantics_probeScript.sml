load "dataSemTheory";
open HolKernel Parse boolLib bossLib;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then (print label; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "evaluate_safe=" dataSemTheory.evaluate_safe_def;
val _ = show "evaluate_peak=" dataSemTheory.evaluate_peak_def;
val _ = show "semantics=" dataSemTheory.semantics_def;
val _ = show "safe_for_space=" dataSemTheory.data_lang_safe_for_space_def;
val _ = show "compute_limits=" dataSemTheory.compute_limits_def;
val _ = show "limits_example=" (EVAL ``dataSem$compute_limits 7 T F T (123,456)``);
val _ = show "safe_skip=" (EVAL ``dataSem$evaluate_safe dataLang$Skip (s:('c,'ffi) dataSem$state)``);
val _ = show "peak_skip=" (EVAL ``dataSem$evaluate_peak dataLang$Skip (s:('c,'ffi) dataSem$state)``);
val _ = show "missing_entry=" (SIMP_RULE (srw_ss()) [] (EVAL ``dataSem$semantics ffi sptree$LN oracle compiler (lm:dataSem$limits) sizes 0``));
