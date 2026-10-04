load "preamble"; load "miscTheory"; load "addressTheory"; load "alignmentTheory";
open HolKernel Parse bossLib preamble;
val _ = Globals.linewidth := 1000000;
val _ = if null (hyp miscTheory.fun2set_disjoint_union) then () else raise Fail "hypotheses: fun2set_disjoint_union";
val _ = (print "fun2set_disjoint_union_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl miscTheory.fun2set_disjoint_union); print "\n");
val _ = if null (hyp addressTheory.word_arith_lemma2) then () else raise Fail "hypotheses: word_arith_lemma2";
val _ = (print "word_arith_lemma2_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl addressTheory.word_arith_lemma2); print "\n");
val _ = if null (hyp alignmentTheory.aligned_add_sub) then () else raise Fail "hypotheses: aligned_add_sub";
val _ = (print "aligned_add_sub_typed="; Lib.with_flag (Globals.show_types,true) print_term (concl alignmentTheory.aligned_add_sub); print "\n");
