load "preamble"; load "wordPropsTheory";
open HolKernel Parse boolLib bossLib preamble wordPropsTheory;
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp (evaluate_code_only_grows)) then () else raise Fail "hypotheses: evaluate_code_only_grows";
val _ = (print "evaluate_code_only_grows_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (evaluate_code_only_grows)); print "\n");
val _ = if null (hyp (evaluate_NONE_stack_size_const)) then () else raise Fail "hypotheses: evaluate_NONE_stack_size_const";
val _ = (print "evaluate_NONE_stack_size_const_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (evaluate_NONE_stack_size_const)); print "\n");
