load "pan_to_wordProofTheory";
open HolKernel Parse boolLib bossLib pan_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp (every_inst_ok_loop_call)) then () else raise Fail "hypotheses: every_inst_ok_loop_call";
val _ = (print "every_inst_ok_loop_call_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (every_inst_ok_loop_call)); print "\n");
val _ = if null (hyp (every_inst_ok_loop_live)) then () else raise Fail "hypotheses: every_inst_ok_loop_live";
val _ = (print "every_inst_ok_loop_live_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (every_inst_ok_loop_live)); print "\n");
val _ = if null (hyp (every_inst_ok_less_optimise)) then () else raise Fail "hypotheses: every_inst_ok_less_optimise";
val _ = (print "every_inst_ok_less_optimise_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (every_inst_ok_less_optimise)); print "\n");
