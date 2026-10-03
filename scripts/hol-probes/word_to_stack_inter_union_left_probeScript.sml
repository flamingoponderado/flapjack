load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory sptreeTheory;
val _ = Globals.linewidth := 1000000;
val original = word_to_stackProofTheory.inter_union_left;
val replay = GEN_ALL(prove(concl original,
  rw[] >> DEP_REWRITE_TAC[spt_eq_thm] >>
  simp[lookup_inter,lookup_union,AllCaseEqs()] >>
  metis_tac[option_CLAUSES]));
val _ = if null(hyp replay) andalso null(free_vars(concl replay)) then () else raise Fail "open inter union theorem";
val _ = if aconv (concl replay) (concl(GEN_ALL original)) then () else raise Fail "statement drift";
val _ = (print "inter_union_left_statement="; print_term(concl replay); print "\n");
val _ = print("inter_union_left_proved=" ^ term_to_string(rhs(concl(EQT_INTRO replay))) ^ "\n");
val _ = print("inter_union_left_hypotheses=" ^ Int.toString(length(hyp replay)) ^ "\n");
