load "preamble"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble word_to_stackProofTheory word_to_stackTheory
  wordSemTheory stackSemTheory wordLangTheory stackLangTheory wordConvsTheory
  wordPropsTheory miscTheory sptreeTheory finite_mapTheory;
val _ = Globals.linewidth := 1000000;
val _ = (print "init_state_ok_definition="; print_term(concl init_state_ok_def));
val _ = print("init_state_ok_hypotheses=" ^ Int.toString(length(hyp init_state_ok_def)) ^ "\n");
val _ = (print "init_state_ok_type="; print_type(type_of ``word_to_stackProof$init_state_ok``); print "\n");
val full = GEN_ALL(prove(``lookup raise_stub_location t.code = SOME (raise_stub F k) /\
   lookup store_consts_stub_location t.code = SOME (store_consts_stub k) /\
    (!n word_prog arg_count.
       (lookup n code = SOME (arg_count,word_prog)) ==>
       post_alloc_conventions k word_prog /\
       flat_exp_conventions word_prog /\
       ?bs i bs2 i2 f stack_prog.
         word_to_stack$compile_prog ac F word_prog arg_count k (bs,i) = (stack_prog,f,(bs2,i2)) /\
         LENGTH (append bs) ≤ i ∧ i - LENGTH (append bs) ≤ LENGTH t.bitmaps /\
         isPREFIX (append bs2) (DROP (i - LENGTH (append bs)) t.bitmaps) /\
         (lookup n t.code = SOME stack_prog)) /\
    domain t.code =
      raise_stub_location INSERT store_consts_stub_location INSERT domain code ∧
    init_state_ok ac k t coracle ==>
    state_rel ac k 0 0 (make_init ac k t code coracle) (t:('a,'c,'ffi)stackSem$state) [] 0``,
fs [state_rel_def,make_init_def,LET_DEF,lookup_def,init_state_ok_def,stack_size_rel_iff]
   \\ strip_tac
   \\ conj_tac>-
     (rw[] >> res_tac >>
      goal_assum old_drule >> rw[lookup_mapi,miscTheory.the_def] >>
      qpat_x_assum `compile_prog _ _ _ _ _ _ = _` mp_tac >>
      rpt(pop_assum kall_tac) >>
      rw[compile_prog_def,ELIM_UNCURRY])
   \\ fs [stack_rel_def,sorted_env_def,abs_stack_def,LET_THM]
   \\ fs [handler_val_def,LASTN_def,stack_rel_aux_def]
   \\ fs [filter_bitmap_def,MAP_FST_def,index_list_def]
   \\ fs[flookup_thm,wf_def] \\ every_case_tac \\ fs []
   \\ fs [lookup_insert,lookup_def] \\ rpt var_eq_tac
   \\ fs [sptreeTheory.wf_def,Once insert_def,lookup_insert]
   \\ fs[stack_size_def,miscTheory.the_def]
   \\ qmatch_asmsub_abbrev_tac `a1 = [a2]`
   \\ `LENGTH a1 = 1` by simp[]
   \\ unabbrev_all_tac
   \\ fs[LENGTH_DROP]));
val _ = if null(hyp full) andalso null(free_vars(concl full)) then () else raise Fail "open theorem";
val _ = (print "initial_state_relation_statement="; print_term(concl full));
val _ = print("initial_state_relation_proved=" ^ term_to_string(rhs(concl(EQT_INTRO full))) ^ "\n");
val _ = print("initial_state_relation_hypotheses=" ^ Int.toString(length(hyp full)) ^ "\n");
