load "backendTheory";
open HolKernel Parse boolLib bossLib backendTheory;
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp (prim_src_config_def)) then () else raise Fail "hypotheses: prim_src_config_def";
val _ = (print "prim_src_config_def_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (prim_src_config_def)); print "\n");
val _ = if null (hyp (prim_src_config_eq)) then () else raise Fail "hypotheses: prim_src_config_eq";
val _ = (print "prim_src_config_eq_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (prim_src_config_eq)); print "\n");
