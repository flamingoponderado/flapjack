load "bvi_letProofTheory";
load "preamble";
open preamble bvi_letProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = Globals.show_types := true;
fun show label th = if null (hyp th) then
  (print label; print "="; print_term (concl th); print "\n")
  else raise Fail (label ^ " has hypotheses");
val _ = show "v_rel" v_rel_def;
val _ = show "env_rel" env_rel_def;
val _ = show "env_rel_length" env_rel_length;
val _ = show "env_rel_MAP" env_rel_MAP;
val _ = show "evaluate_env_rel" evaluate_env_rel;
val _ = show "compile_thm" compile_thm;
val _ = show "evaluate_compile_exp" evaluate_compile_exp;
val _ = show "dest_var_code_labels" dest_var_code_labels;
val _ = show "compile_code_labels" compile_code_labels;
val _ = show "compile_exp_code_labels" compile_exp_code_labels;
