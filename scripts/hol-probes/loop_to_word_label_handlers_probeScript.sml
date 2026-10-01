load "preamble";
load "loop_to_wordProofTheory";
open bossLib HolKernel Parse preamble loop_to_wordProofTheory loop_to_wordTheory wordConvsTheory;
val comp_l_invariant = GEN_ALL(prove(``∀ctxt prog l prog' l'. comp ctxt prog l = (prog',l') ⇒ FST l' = FST l``, ho_match_mp_tac comp_ind >>
  rw[comp_def] >>
  gvs[ELIM_UNCURRY,PULL_FORALL,AllCaseEqs()] >> metis_tac[PAIR]));
val _ = (print "comp_l_invariant_source_replay="; print_thm comp_l_invariant; print "\n");
val good_handlers_comp = GEN_ALL(prove(``∀ctxt prog l. good_handlers (FST l) (FST (comp ctxt prog l))``, ho_match_mp_tac comp_ind >>
  rw[good_handlers_def,
     comp_def] >>
  gvs[ELIM_UNCURRY] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
  metis_tac[PAIR,FST,SND,comp_l_invariant]));
val _ = (print "good_handlers_comp_source_replay="; print_thm good_handlers_comp; print "\n");
val loop_to_word_good_handlers = GEN_ALL(prove(``(compile_prog prog) = prog' ⇒
  EVERY (λ(n,m,pp). good_handlers n pp) prog'``, fs[compile_def,
     compile_prog_def,
     comp_func_def]>>
  rw[]>>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
  PairCases >>
  rw[] >>
  pop_assum kall_tac >>
  rename1 ‘comp ctxt prog’ >>
  rename1 ‘(n,m)’ >>
  metis_tac[PAIR,FST,SND,good_handlers_comp]));
val _ = (print "loop_to_word_good_handlers_source_replay="; print_thm loop_to_word_good_handlers; print "\n");
val loop_to_word_comp_SND_LE = GEN_ALL(prove(``∀ctxt prog l p r.
    comp ctxt prog l = (p,r) ⇒
    SND l ≤ SND r``, ho_match_mp_tac loop_to_wordTheory.comp_ind>>
  rw[loop_to_wordTheory.comp_def]>>
  rpt (FULL_CASE_TAC>>gs[])>>gvs[]>>
  pairarg_tac>>gs[]>>pairarg_tac>>gs[]>>
  rveq>>gs[]));
val _ = (print "loop_to_word_comp_SND_LE_source_replay="; print_thm loop_to_word_comp_SND_LE; print "\n");

fun out label th = (print(label ^ "="); print_term(rconc th); print "\n");
fun application context source labels = let
 val evaluation = EVAL ``comp ^context ^source ^labels``
 val (program,finalLabels) = dest_pair(rhs(concl evaluation))
 val first = MATCH_MP (ISPECL [context,source,labels,program,finalLabels] comp_l_invariant) evaluation
 val second = MATCH_MP (ISPECL [context,source,labels,program,finalLabels] loop_to_word_comp_SND_LE) evaluation
 val handlers = ISPECL [context,source,labels] good_handlers_comp
 val _ = if List.all (fn th => null(hyp th)) [first,second,handlers] then () else raise Fail "unexpected premise"
 in (evaluation,EQT_INTRO first,EQT_INTRO second,EQT_INTRO handlers) end;
val leaf64 = ``loopLang$Call (SOME ([],LN)) (SOME 5) [1] NONE :64 word loopLang$prog``;
val nested64 = ``loopLang$Call (SOME ([2],LN)) NONE [1]
 (SOME (3,^leaf64,loopLang$Seq (loopLang$LocValue 4 6) (loopLang$Mark ^leaf64),LN))``;
val (lh_nested64_result,lh_nested64_owner,lh_nested64_counter,lh_nested64_handlers) = application ``LN:num num_map`` nested64 ``(42:num,9:num)``;
val _ = out "lh_nested64_result" lh_nested64_result;
val _ = out "lh_nested64_owner" lh_nested64_owner;
val _ = out "lh_nested64_counter" lh_nested64_counter;
val _ = out "lh_nested64_handlers" lh_nested64_handlers;
val leaf1 = ``loopLang$Call (SOME ([],LN)) (SOME 5) [1] NONE :1 word loopLang$prog``;
val nested1 = ``loopLang$Call (SOME ([2],LN)) NONE [1]
 (SOME (3,^leaf1,loopLang$Seq (loopLang$LocValue 4 6) (loopLang$Mark ^leaf1),LN))``;
val (lh_nested1_result,lh_nested1_owner,lh_nested1_counter,lh_nested1_handlers) = application ``LN:num num_map`` nested1 ``(42:num,9:num)``;
val _ = out "lh_nested1_result" lh_nested1_result;
val _ = out "lh_nested1_owner" lh_nested1_owner;
val _ = out "lh_nested1_counter" lh_nested1_counter;
val _ = out "lh_nested1_handlers" lh_nested1_handlers;
val leaf80 = ``loopLang$Call (SOME ([],LN)) (SOME 5) [1] NONE :80 word loopLang$prog``;
val nested80 = ``loopLang$Call (SOME ([2],LN)) NONE [1]
 (SOME (3,^leaf80,loopLang$Seq (loopLang$LocValue 4 6) (loopLang$Mark ^leaf80),LN))``;
val (lh_nested80_result,lh_nested80_owner,lh_nested80_counter,lh_nested80_handlers) = application ``LN:num num_map`` nested80 ``(42:num,9:num)``;
val _ = out "lh_nested80_result" lh_nested80_result;
val _ = out "lh_nested80_owner" lh_nested80_owner;
val _ = out "lh_nested80_counter" lh_nested80_counter;
val _ = out "lh_nested80_handlers" lh_nested80_handlers;
val (lh_ignored_tail_result,lh_ignored_tail_owner,lh_ignored_tail_counter,lh_ignored_tail_handlers) = application ``LN:num num_map``
 ``loopLang$Call NONE (SOME 5) [1] (SOME (3,^nested64,^nested64,LN))`` ``(42:num,9:num)``;
val _ = out "lh_ignored_tail_result" lh_ignored_tail_result;
val _ = out "lh_ignored_tail_owner" lh_ignored_tail_owner;
val _ = out "lh_ignored_tail_counter" lh_ignored_tail_counter;
val _ = out "lh_ignored_tail_handlers" lh_ignored_tail_handlers;
val rows = ``[(42:num,[]:num list,^nested64);(42:num,[1]:num list,^leaf64)]``;
val compiled = EVAL ``compile_prog ^rows``;
val listHandlers = MATCH_MP (ISPECL [rhs(concl compiled),rows] loop_to_word_good_handlers) compiled;
val _ = if null(hyp listHandlers) then () else raise Fail "unexpected list premise";
val _ = out "lh_program_result" compiled;
val _ = out "lh_program_handlers" (EQT_INTRO listHandlers);
val _ = out "lh_wrong_owner" (EVAL ``good_handlers 42
 (wordLang$Call (SOME ([],(LN,LN),wordLang$Skip,42,9)) NONE []
 (SOME (0,wordLang$Skip,43,10)):64 word wordLang$prog)``);
