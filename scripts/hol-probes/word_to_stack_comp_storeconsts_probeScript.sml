load "preamble"; load "helperLib"; load "word_to_stackProofTheory";
open HolKernel Parse bossLib preamble BasicProvers helperLib word_to_stackProofTheory
 word_to_stackTheory wordSemTheory stackSemTheory wordLangTheory stackLangTheory;
val _ = Globals.linewidth := 1000000;
val motive = ``
   λ(prog:'a wordLang$prog,s:('a,num # 'c,'ffi) wordSem$state).
     ∀k f f' res s1 t bs n bs' n' sprog lens.
     (wordSem$evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
     state_rel ac k f f' s t lens 0 /\
     post_alloc_conventions k prog /\
     flat_exp_conventions prog /\
     comp ac F prog (bs,n) (k,f,f') = (sprog, (bs',n')) /\
     LENGTH (append bs) ≤ n ∧ n - LENGTH (append bs) ≤ LENGTH t.bitmaps ∧
     isPREFIX (append bs') (DROP (n - LENGTH (append bs)) t.bitmaps) ∧
     get_labels sprog SUBSET loc_check t.code /\
     max_var prog < 2 * f' + 2 * k ==>
     ?ck t1:('a,'c,'ffi) stackSem$state res1.
       (stackSem$evaluate (sprog,t with clock := t.clock + ck) = (res1,t1)) /\
       if OPTION_MAP compile_result res <> res1
       then res1 = SOME (Halt (Word 2w)) /\
            t1.ffi.io_events ≼ s1.ffi.io_events /\
            the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
       else
         case res of
         | NONE => state_rel ac k f f' s1 t1 lens 0
         | SOME (Result _ ys) =>
            state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
            (∀i. i < LENGTH ys ==> (if i + 1 < k then
              (FLOOKUP t1.regs (i+1) = SOME (EL i ys)) else
            (LLOOKUP (DROP t1.stack_space t1.stack) (LENGTH ys - (i + 1)) = SOME (EL i ys))))
         | SOME (Exception _ y) =>
           ∃l0 l.
           state_rel ac k 0 0 (push_locals l0 l s1) t1 (LASTN (s.handler+1) lens) 0 /\
           s1.locals = union (fromAList l) (fromAList l0) ∧
           FLOOKUP t1.regs 1 = SOME y
         | SOME (Break _) => state_rel ac k f f' s1 t1 lens 0
         | SOME (Continue _) => state_rel ac k f f' s1 t1 lens 0
         | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock``;
val ind = wordSemTheory.evaluate_ind |> ISPEC motive |> GEN_BETA_RULE;
val obligations = ind |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj;
val getCase = first (can (find_term (can (match_term ``wordLang$StoreConsts r1 r2 r3 r4 words``)))) obligations;
val whole = GEN_ALL (Q.SPECL [`wordLang$StoreConsts r1 r2 r3 r4 words`, `s`] word_to_stackProofTheory.comp_correct);
open preamble semanticsPropsTheory stackSemTheory wordSemTheory word_to_stackTheory
  wordPropsTheory wordConvsTheory stackPropsTheory parmoveTheory helperLib;
val _ = temp_delsimps ["NORMEQ_CONV"];
val _ = diminish_srw_ss ["ABBREV"];
val _ = temp_delsimps ["fromAList_def", "domain_union", "domain_insert",
  "domain_inter", "domain_map", "domain_difference", "sptree.map_def",
  "sptree.lookup_rwts", "sptree.insert_notEmpty", "misc.max3_def"];
val _ = numLib.temp_prefer_num();
val get_labels_def = stackSemTheory.get_labels_def;
val callTh = GEN_ALL(prove(getCase,
gvs [wordSemTheory.evaluate_def,AllCaseEqs(),PULL_EXISTS]
  \\ rpt strip_tac \\ gvs [comp_def]
  \\ pairarg_tac \\ gvs []
  \\ qexists_tac ‘0’
  \\ ‘t.use_store ∧ t.use_alloc ∧ good_dimindex (:'a)’ by fs [state_rel_def]
  \\ gvs [stackSemTheory.evaluate_def,stackSemTheory.inst_def,stackSemTheory.assign_def,
          stackSemTheory.word_exp_def,post_alloc_conventions_def,call_arg_convention_def]
  \\ IF_CASES_TAC
  THEN1
   (qsuff_tac ‘F’ \\ fs []
    \\ fs [check_store_consts_opt_def]
    \\ gvs [state_rel_def,store_consts_stub_def])
  \\ gvs [store_const_sem_def]
  \\ IF_CASES_TAC THEN1 fs [state_rel_def] \\ fs []
  \\ fs [stackSemTheory.get_var_def,stackSemTheory.set_var_def,lookup_insert,
         FLOOKUP_UPDATE]
  \\ ‘FLOOKUP t.regs 2 = SOME (Word a) ∧ FLOOKUP t.regs 3 = SOME (Word off)’ by
    (fs [state_rel_def,get_var_def] \\ res_tac \\ ‘3 < k’ by fs [] \\ fs [])
  \\ fs [stackSemTheory.unset_var_def]
  \\ ‘LENGTH t.bitmaps < dimword (:α)’ by fs [state_rel_def]
  \\ ‘∃xs ys. t.bitmaps = xs ++ const_words_to_bitmap words (LENGTH words) ++ ys ∧
              LENGTH xs = i’ by (
    fs[insert_bitmap_def]>>rw[]>>
    fs[append_thm]>>
    old_drule isPREFIX_DROP>>
    disch_then(qspec_then`LENGTH(append bs)` mp_tac)>>
    simp[DROP_APPEND,DROP_LENGTH_NIL]>>
    DEP_REWRITE_TAC[DROP_DROP]>> simp[]>>
    old_drule IS_PREFIX_LENGTH>> simp[]>>
    strip_tac>>
    gvs [IS_PREFIX_APPEND]>>
    strip_tac>>
    qexists_tac`TAKE i t.bitmaps`>>qexists_tac`l'`>>simp[]>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>> pop_assum sym_sub_tac>>
    simp[])
  \\ gvs []
  \\ ‘s.mdomain = t.mdomain’ by fs [state_rel_def]
  \\ old_drule (GEN_ALL copy_words_correct)
  \\ fs [] \\ disch_then kall_tac
  \\ fs [state_rel_def,set_var_def,unset_var_def,lookup_insert]
  \\ rpt strip_tac
  \\ TRY (res_tac \\ NO_TAC)
  \\ rpt (irule wf_insert)
  \\ rpt (irule wf_delete)
  \\ fs []\\ gvs [AllCaseEqs(),lookup_delete]
  \\ gvs [DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
  \\ fs [DIV_LT_X]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [DIV_EQ_X]
  \\ res_tac
  \\ rename1`nn < 2 * k`
  \\ Cases_on ‘nn’ \\ fs []
  \\ rename1`SUC nn < 2 * k`
  \\ Cases_on ‘nn’ \\ fs [ADD1]
  \\ rename1`nn + 2 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs []
  \\ rename1`SUC nn + 2 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs [ADD1]
  \\ rename1`nn + 4 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs []
  \\ rename1`SUC nn + 4 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs [ADD1]
  \\ rw [] \\ fs []));
val _ = if null(hyp whole) andalso null(free_vars(concl whole)) andalso
  null(hyp callTh) andalso null(free_vars(concl callTh)) then () else raise Fail "open case";
val _ = (print "comp_correct_storeconsts_full_statement="; print_term(concl callTh); print "\n");
val _ = print("comp_correct_storeconsts_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO callTh))) ^ "\n");
val _ = print("comp_correct_storeconsts_full_hypotheses=" ^ Int.toString(length(hyp callTh)) ^ "\n");
val _ = (print "comp_correct_storeconsts_whole_statement="; print_term(concl whole); print "\n");
val _ = print("comp_correct_storeconsts_whole_proved=" ^ term_to_string(rhs(concl(EQT_INTRO whole))) ^ "\n");
val _ = print("comp_correct_storeconsts_whole_hypotheses=" ^ Int.toString(length(hyp whole)) ^ "\n");
