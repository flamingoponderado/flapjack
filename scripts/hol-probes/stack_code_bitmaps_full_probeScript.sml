load "preamble"; load "stackPropsTheory";
open HolKernel Parse bossLib preamble stackPropsTheory stackLangTheory stackSemTheory miscTheory;
val _ = Globals.linewidth := 1000000;
val full = prove(concl evaluate_code_bitmaps,
  recInduct evaluate_ind >>
  rpt conj_tac >>
  simp[evaluate_def] >>
  rpt (gen_tac ORELSE disch_tac) >>
  gvs[AllCaseEqs(),UNCURRY_EQ] >>
  map_every imp_res_tac [alloc_const,inst_const,store_const_sem_const,sh_mem_op_const] >>
  fs[shift_seq_def] >>
  TRY(qexists_tac`0` \\ fsrw_tac[ETA_ss][] \\ NO_TAC) >>
  PURE_REWRITE_TAC[GSYM FLAT_APPEND,GSYM MAP_APPEND,GSYM GENLIST_APPEND,GSYM FOLDL_APPEND] >>
  TRY ( qmatch_goalsub_abbrev_tac `s.compile_oracle (_ + N)`>>
  qexists_tac `N` >> fsrw_tac[ETA_ss][Abbr`N`] \\ NO_TAC));
val _ = if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
val _ = (print "bitmap_full_statement="; print_term(concl full));
val _ = print("bitmap_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO full))) ^ "\n");
val _ = print("bitmap_full_hypotheses=" ^ Int.toString(length(hyp full)) ^ "\n");
val _ = (print "bitmap_full_type="; print_type(type_of(concl full)));
