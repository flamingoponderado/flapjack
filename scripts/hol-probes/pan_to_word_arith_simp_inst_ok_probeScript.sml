load "pan_to_wordProofTheory";
open HolKernel Parse boolLib bossLib pan_to_wordProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp (every_inst_ok_arith_simp_exp)) then () else raise Fail "hypotheses: every_inst_ok_arith_simp_exp";
val _ = (print "every_inst_ok_arith_simp_exp_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (every_inst_ok_arith_simp_exp)); print "\n");
val _ = if null (hyp (every_inst_ok_arith_simp_prog)) then () else raise Fail "hypotheses: every_inst_ok_arith_simp_prog";
val _ = (print "every_inst_ok_arith_simp_prog_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (every_inst_ok_arith_simp_prog)); print "\n");
val _ = if null (hyp (every_inst_ok_less_crep_to_loop_compile_prog)) then () else raise Fail "hypotheses: every_inst_ok_less_crep_to_loop_compile_prog";
val _ = (print "every_inst_ok_less_crep_to_loop_compile_prog_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (every_inst_ok_less_crep_to_loop_compile_prog)); print "\n");
