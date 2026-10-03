load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory
  stackSemTheory wordSemTheory wordLangTheory stackLangTheory sptreeTheory finite_mapTheory;
val _ = Globals.linewidth := 1000000;
val th = GEN_ALL(prove(``state_rel ac k f f' s t lens extra ⇒
  domain s.code ⊆ domain t.code``,
  strip_tac>>fs[state_rel_def,SUBSET_DEF,domain_lookup,EXISTS_PROD]>>
  metis_tac[]));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
val _ = (print "state_rel_code_domain_statement="; print_term(concl th));
val _ = print("state_rel_code_domain_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("state_rel_code_domain_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val th = GEN_ALL(prove(``!xs p. get_labels (wStackLoad xs p) = get_labels p``,
  Induct \\ fs [wStackLoad_def]
  \\ Cases \\ fs [wStackLoad_def,get_labels_def]));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
val _ = (print "get_labels_wStackLoad_statement="; print_term(concl th));
val _ = print("get_labels_wStackLoad_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("get_labels_wStackLoad_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
val th = GEN_ALL(prove(``subspt s t ⇒
  loc_check s ⊆ loc_check t``,
  fs[SUBSET_DEF,IN_DEF,loc_check_def,FORALL_PROD,subspt_def]>>rw[]>>
  metis_tac[domain_lookup,IN_DEF]));
val _ = if null(hyp th) andalso null(free_vars(concl th)) then () else raise Fail "open theorem";
val _ = (print "loc_check_SUBSET_statement="; print_term(concl th));
val _ = print("loc_check_SUBSET_proved=" ^ term_to_string(rhs(concl(EQT_INTRO th))) ^ "\n");
val _ = print("loc_check_SUBSET_hypotheses=" ^ Int.toString(length(hyp th)) ^ "\n");
