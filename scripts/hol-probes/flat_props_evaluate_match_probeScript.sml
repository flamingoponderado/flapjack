load "flatPropsTheory";
open HolKernel Parse boolLib bossLib;
open flatPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = set_trace "Unicode" 0;
val _ = (print "evaluate_match_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl evaluate_match_def); print "\n");

val _ = if null (hyp flatPropsTheory.build_rec_env_eq_MAP) then () else raise Fail "build_rec_env_eq_MAP has hypotheses";
val _ = (print "build_rec_env_eq_MAP_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl flatPropsTheory.build_rec_env_eq_MAP); print "\n");
