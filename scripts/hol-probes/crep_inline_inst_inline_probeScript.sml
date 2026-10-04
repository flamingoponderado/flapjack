load "preamble";
load "crep_inlineProofTheory";
open HolKernel Parse bossLib preamble crep_inlineProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp (exps_of_inst_inline)) then () else raise Fail "hypotheses: exps_of_inst_inline";
val _ = (print "exps_of_inst_inline_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (exps_of_inst_inline)); print "\n");
val _ = if null (hyp (every_inst_crep_inline)) then () else raise Fail "hypotheses: every_inst_crep_inline";
val _ = (print "every_inst_crep_inline_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (every_inst_crep_inline)); print "\n");
