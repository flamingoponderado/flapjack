load "preamble"; load "miscTheory";
open HolKernel Parse bossLib preamble miscTheory;
val _ = Globals.linewidth := 1000000;
val original = GEN_ALL (DB.fetch "misc" "EVEN_fromList2");
val _ = if null(hyp original) andalso null(free_vars(concl original)) then () else raise Fail "open theorem";
val _ = (print "even_from_list2_statement="; print_term(concl original); print "\n");
val _ = print("even_from_list2_proved=" ^ term_to_string(rhs(concl(EQT_INTRO original))) ^ "\n");
val _ = print("even_from_list2_hypotheses=" ^ Int.toString(length(hyp original)) ^ "\n");
