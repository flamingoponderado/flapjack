load "preamble"; load "word_depthProofTheory";
open HolKernel Parse boolLib bossLib preamble word_depthProofTheory;
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp (max_depth_call_graph_lemma)) then () else raise Fail "hypotheses: max_depth_call_graph_lemma";
val _ = (print "max_depth_call_graph_lemma_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (max_depth_call_graph_lemma)); print "\n");
val _ = if null (hyp (max_depth_call_graph)) then () else raise Fail "hypotheses: max_depth_call_graph";
val _ = (print "max_depth_call_graph_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (max_depth_call_graph)); print "\n");
val _ = if null (hyp (max_depth_Call_NONE)) then () else raise Fail "hypotheses: max_depth_Call_NONE";
val _ = (print "max_depth_Call_NONE_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl (max_depth_Call_NONE)); print "\n");
