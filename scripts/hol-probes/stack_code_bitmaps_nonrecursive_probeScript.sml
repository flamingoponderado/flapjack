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
val _ = (print "nonrec_full_statement="; print_term(concl full));
val _ = print("nonrec_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO full))) ^ "\n");
val _ = (print "nonrec_skip_statement="; print_term(concl(ISPEC ``stackLang$Skip:64 stackLang$prog`` full)));
val _ = (print "nonrec_halt_statement="; print_term(concl(ISPEC ``stackLang$Halt v:64 stackLang$prog`` full)));
val _ = (print "nonrec_ret_statement="; print_term(concl(ISPEC ``stackLang$Return n:64 stackLang$prog`` full)));
val _ = (print "nonrec_raise_statement="; print_term(concl(ISPEC ``stackLang$Raise n:64 stackLang$prog`` full)));
val _ = (print "nonrec_break_statement="; print_term(concl(ISPEC ``stackLang$Break n:64 stackLang$prog`` full)));
val _ = (print "nonrec_continue_statement="; print_term(concl(ISPEC ``stackLang$Continue n:64 stackLang$prog`` full)));
val _ = (print "nonrec_get_statement="; print_term(concl(ISPEC ``stackLang$Get v name:64 stackLang$prog`` full)));
val _ = (print "nonrec_set_statement="; print_term(concl(ISPEC ``stackLang$Set name v:64 stackLang$prog`` full)));
val _ = (print "nonrec_opCurrHeap_statement="; print_term(concl(ISPEC ``stackLang$OpCurrHeap binop v src:64 stackLang$prog`` full)));
val _ = (print "nonrec_tick_statement="; print_term(concl(ISPEC ``stackLang$Tick:64 stackLang$prog`` full)));
val _ = (print "nonrec_locValue_statement="; print_term(concl(ISPEC ``stackLang$LocValue r l1 l2:64 stackLang$prog`` full)));
val _ = (print "nonrec_stackAlloc_statement="; print_term(concl(ISPEC ``stackLang$StackAlloc n:64 stackLang$prog`` full)));
val _ = (print "nonrec_stackFree_statement="; print_term(concl(ISPEC ``stackLang$StackFree n:64 stackLang$prog`` full)));
val _ = (print "nonrec_stackLoad_statement="; print_term(concl(ISPEC ``stackLang$StackLoad r n:64 stackLang$prog`` full)));
val _ = (print "nonrec_stackLoadAny_statement="; print_term(concl(ISPEC ``stackLang$StackLoadAny r rn:64 stackLang$prog`` full)));
val _ = (print "nonrec_stackStore_statement="; print_term(concl(ISPEC ``stackLang$StackStore r n:64 stackLang$prog`` full)));
val _ = (print "nonrec_stackStoreAny_statement="; print_term(concl(ISPEC ``stackLang$StackStoreAny r rn:64 stackLang$prog`` full)));
val _ = (print "nonrec_stackGetSize_statement="; print_term(concl(ISPEC ``stackLang$StackGetSize r:64 stackLang$prog`` full)));
val _ = (print "nonrec_stackSetSize_statement="; print_term(concl(ISPEC ``stackLang$StackSetSize r:64 stackLang$prog`` full)));
val _ = (print "nonrec_bitmapLoad_statement="; print_term(concl(ISPEC ``stackLang$BitmapLoad r v:64 stackLang$prog`` full)));
val _ = (print "nonrec_codeBufferWrite_statement="; print_term(concl(ISPEC ``stackLang$CodeBufferWrite r1 r2:64 stackLang$prog`` full)));
val _ = (print "nonrec_dataBufferWrite_statement="; print_term(concl(ISPEC ``stackLang$DataBufferWrite r1 r2:64 stackLang$prog`` full)));
val _ = (print "nonrec_shMemOp_statement="; print_term(concl(ISPEC ``stackLang$ShMemOp op r (Addr a w):64 stackLang$prog`` full)));
